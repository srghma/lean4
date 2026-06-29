// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Tactic.Grind.Arith.CommRing.RingId Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.Tactic.Grind.Arith.Cutsat.Var Lean.Meta.Tactic.Grind.Arith.CommRing.Reify Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly
use crate::r#gen::Init::Data::Int::Linear::l_Int_Linear_instBEqPoly_beq;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_get_x21___redArg, l_Lean_PersistentArray_push___redArg,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_isAppOf, l_Lean_Nat_mkType, l_Lean_instInhabitedExpr,
    l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkNatLit,
    l_Lean_mkRawNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Sym::Canon::l_Lean_Meta_Sym_canon;
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getIntExpr___redArg, l_Lean_Meta_Sym_shareCommon___redArg,
};
use crate::r#gen::Lean::Meta::Sym::SynthInstance::l_Lean_Meta_Sym_synthInstanceMeta_x3f;
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_synthInstance_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::DenoteExpr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Functions::l_Lean_Meta_Grind_Arith_CommRing_checkInst;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Reify::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify,
    l_Lean_Meta_Grind_Arith_CommRing_reify_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::RingId::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId,
    l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::RingM::{
    l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing,
    l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::SafePoly::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly,
    l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types, l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util, l_Int_Linear_Poly_denoteExpr_x27___redArg,
    l_Int_Linear_Poly_pp___redArg, l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Var::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var, l_Lean_Meta_Grind_Arith_Cutsat_toPoly,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Util::l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
use crate::r#gen::Lean::Meta::Tactic::Grind::Simp::{
    initialize_Lean_Meta_Tactic_Grind_Simp, l_Lean_Meta_Grind_preprocessLight___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Simp,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_getGeneration___redArg,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_eq, lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Types::lean_grind_internalize;
pub static l_Int_Linear_Poly_isNonlinear___redArg___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [72, 77, 117, 108, 0],
};
static mut l_Int_Linear_Poly_isNonlinear___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_Linear_Poly_isNonlinear___redArg___closed__1_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 77, 117, 108, 0],
};
static mut l_Int_Linear_Poly_isNonlinear___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Int_Linear_Poly_isNonlinear___redArg___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        2929883540436775422 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Int_Linear_Poly_isNonlinear___redArg___closed__2_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        1611444129324655608 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Int_Linear_Poly_isNonlinear___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_Linear_Poly_isNonlinear___redArg___closed__3_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [72, 80, 111, 119, 0],
};
static mut l_Int_Linear_Poly_isNonlinear___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_Linear_Poly_isNonlinear___redArg___closed__4_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 80, 111, 119, 0],
};
static mut l_Int_Linear_Poly_isNonlinear___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Int_Linear_Poly_isNonlinear___redArg___closed__5_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        12847922472053947547 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Int_Linear_Poly_isNonlinear___redArg___closed__5_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        10422657989269798688 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Int_Linear_Poly_isNonlinear___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 105, 110, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [82, 105, 110, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 78, 101, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value) as *mut crate::leanh::LeanObject,10806710915646349764 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3_value) as *mut crate::leanh::LeanObject,10040236838748678500 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value) as *mut crate::leanh::LeanObject,9626815015619986526 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__7_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__7_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value) as *mut crate::leanh::LeanObject,9626815015619986526 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__7_value) as *mut crate::leanh::LeanObject,17185717442815859305 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,17636616155771105671 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,17636616155771105671 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,15578568367168711682 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value) as *mut crate::leanh::LeanObject,12050285396929189622 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,9341924117480681831 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 72, 65, 100, 100, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,9594062259507646949 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 65, 100, 100, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value) as *mut crate::leanh::LeanObject,12050285396929189622 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,5442360487226035463 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value) as *mut crate::leanh::LeanObject,10393083817453678557 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value) as *mut crate::leanh::LeanObject,10393083817453678557 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value) as *mut crate::leanh::LeanObject,10680564408669940870 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 72, 77, 117, 108, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,18134279130838690737 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 77, 117, 108, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value) as *mut crate::leanh::LeanObject,12050285396929189622 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2_value) as *mut crate::leanh::LeanObject,7102027102192867304 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__0_value) as *mut crate::leanh::LeanObject,2929883540436775422 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__3_value) as *mut crate::leanh::LeanObject,12847922472053947547 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 112, 111, 119, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value) as *mut crate::leanh::LeanObject,12050285396929189622 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2_value) as *mut crate::leanh::LeanObject,18388652353510661091 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Int_Linear_Poly_normCommRing_x3f___closed__1_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_Linear_Poly_normCommRing_x3f___closed__2_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_Linear_Poly_normCommRing_x3f___closed__3_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [97, 115, 115, 101, 114, 116, 0],
    };
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_Linear_Poly_normCommRing_x3f___closed__4_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [110, 111, 110, 108, 105, 110, 101, 97, 114, 0],
};
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Int_Linear_Poly_normCommRing_x3f___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
            15947788021050471391 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Int_Linear_Poly_normCommRing_x3f___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__5_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__2_value)
                as *mut crate::leanh::LeanObject,
            11074150007773075224 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Int_Linear_Poly_normCommRing_x3f___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__5_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__3_value)
                as *mut crate::leanh::LeanObject,
            10199653630302390726 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Int_Linear_Poly_normCommRing_x3f___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__5_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__4_value)
                as *mut crate::leanh::LeanObject,
            4162367480076971315 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_Linear_Poly_normCommRing_x3f___closed__6_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_Linear_Poly_normCommRing_x3f___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__6_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Int_Linear_Poly_normCommRing_x3f___closed__9_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [32, 61, 61, 61, 62, 32, 0],
    };
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Int_Linear_Poly_isNonlinear___redArg(
    mut v_p_1905_: *mut crate::leanh::LeanObject,
    mut v_a_1906_: *mut crate::leanh::LeanObject,
    mut v_a_1907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1917_: u8 = 0;
    let mut v___y_1919_: u8 = 0;
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: u8 = 0;
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: u8 = 0;
    let mut v_isSharedCheck_1929_: u8 = 0;
    let mut v_a_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1933_: u8 = 0;
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1937_: u8 = 0;
    let mut v_a_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1941_: u8 = 0;
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1945_: u8 = 0;
    let mut v___x_1946_: u8 = 0;
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_1905_) == 1 {
                    v_v_1909_ = crate::leanh::lean_ctor_get(v_p_1905_, 1);
                    v_p_1910_ = crate::leanh::lean_ctor_get(v_p_1905_, 2);
                    v___x_1911_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(
                        v_v_1909_, v_a_1906_, v_a_1907_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1911_) == 0 {
                        v_a_1912_ = crate::leanh::lean_ctor_get(v___x_1911_, 0);
                        crate::leanh::lean_inc(v_a_1912_);
                        crate::leanh::lean_dec_ref_known(v___x_1911_, 1);
                        v___x_1913_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(
                            v_v_1909_, v_a_1906_, v_a_1907_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1913_) == 0 {
                            v_a_1914_ = crate::leanh::lean_ctor_get(v___x_1913_, 0);
                            v_isSharedCheck_1929_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1913_)) as u8;
                            if v_isSharedCheck_1929_ == 0 {
                                v___x_1916_ = v___x_1913_;
                                v_isShared_1917_ = v_isSharedCheck_1929_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1914_);
                                crate::leanh::lean_dec(v___x_1913_);
                                v___x_1916_ = crate::leanh::lean_box(0);
                                v_isShared_1917_ = v_isSharedCheck_1929_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1912_);
                            v_a_1930_ = crate::leanh::lean_ctor_get(v___x_1913_, 0);
                            v_isSharedCheck_1937_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1913_)) as u8;
                            if v_isSharedCheck_1937_ == 0 {
                                v___x_1932_ = v___x_1913_;
                                v_isShared_1933_ = v_isSharedCheck_1937_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1930_);
                                crate::leanh::lean_dec(v___x_1913_);
                                v___x_1932_ = crate::leanh::lean_box(0);
                                v_isShared_1933_ = v_isSharedCheck_1937_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_a_1938_ = crate::leanh::lean_ctor_get(v___x_1911_, 0);
                        v_isSharedCheck_1945_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1911_)) as u8;
                        if v_isSharedCheck_1945_ == 0 {
                            v___x_1940_ = v___x_1911_;
                            v_isShared_1941_ = v_isSharedCheck_1945_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1938_);
                            crate::leanh::lean_dec(v___x_1911_);
                            v___x_1940_ = crate::leanh::lean_box(0);
                            v_isShared_1941_ = v_isSharedCheck_1945_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v___x_1946_ = 0;
                    v___x_1947_ = crate::leanh::lean_box((v___x_1946_) as usize);
                    v___x_1948_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1948_, 0, v___x_1947_);
                    return v___x_1948_;
                }
            }
            1 => {
                v___x_1925_ = l_Int_Linear_Poly_isNonlinear___redArg___closed__2;
                v___x_1926_ = l_Lean_Expr_isAppOf(v_a_1912_, v___x_1925_);
                crate::leanh::lean_dec(v_a_1912_);
                if v___x_1926_ == 0 {
                    v___x_1927_ = l_Int_Linear_Poly_isNonlinear___redArg___closed__5;
                    v___x_1928_ = l_Lean_Expr_isAppOf(v_a_1914_, v___x_1927_);
                    crate::leanh::lean_dec(v_a_1914_);
                    v___y_1919_ = v___x_1928_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_1914_);
                    v___y_1919_ = v___x_1926_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_1919_ == 0 {
                    crate::leanh::lean_del_object(v___x_1916_);
                    v_p_1905_ = v_p_1910_;
                    state = 0;
                    continue;
                } else {
                    v___x_1921_ = crate::leanh::lean_box((v___y_1919_) as usize);
                    if v_isShared_1917_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1916_, 0, v___x_1921_);
                        v___x_1923_ = v___x_1916_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1924_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
                        v___x_1923_ = v_reuseFailAlloc_1924_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1923_;
            }
            4 => {
                if v_isShared_1933_ == 0 {
                    v___x_1935_ = v___x_1932_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1936_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
                    v___x_1935_ = v_reuseFailAlloc_1936_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1935_;
            }
            6 => {
                if v_isShared_1941_ == 0 {
                    v___x_1943_ = v___x_1940_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1944_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
                    v___x_1943_ = v_reuseFailAlloc_1944_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1943_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_isNonlinear___redArg___boxed(
    mut v_p_1949_: *mut crate::leanh::LeanObject,
    mut v_a_1950_: *mut crate::leanh::LeanObject,
    mut v_a_1951_: *mut crate::leanh::LeanObject,
    mut v_a_1952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1953_ = l_Int_Linear_Poly_isNonlinear___redArg(v_p_1949_, v_a_1950_, v_a_1951_);
    crate::leanh::lean_dec_ref(v_a_1951_);
    crate::leanh::lean_dec(v_a_1950_);
    crate::leanh::lean_dec_ref(v_p_1949_);
    return v_res_1953_;
}
pub unsafe fn l_Int_Linear_Poly_isNonlinear(
    mut v_p_1954_: *mut crate::leanh::LeanObject,
    mut v_a_1955_: *mut crate::leanh::LeanObject,
    mut v_a_1956_: *mut crate::leanh::LeanObject,
    mut v_a_1957_: *mut crate::leanh::LeanObject,
    mut v_a_1958_: *mut crate::leanh::LeanObject,
    mut v_a_1959_: *mut crate::leanh::LeanObject,
    mut v_a_1960_: *mut crate::leanh::LeanObject,
    mut v_a_1961_: *mut crate::leanh::LeanObject,
    mut v_a_1962_: *mut crate::leanh::LeanObject,
    mut v_a_1963_: *mut crate::leanh::LeanObject,
    mut v_a_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1966_ = l_Int_Linear_Poly_isNonlinear___redArg(v_p_1954_, v_a_1955_, v_a_1963_);
    return v___x_1966_;
}
pub unsafe fn l_Int_Linear_Poly_isNonlinear___boxed(
    mut v_p_1967_: *mut crate::leanh::LeanObject,
    mut v_a_1968_: *mut crate::leanh::LeanObject,
    mut v_a_1969_: *mut crate::leanh::LeanObject,
    mut v_a_1970_: *mut crate::leanh::LeanObject,
    mut v_a_1971_: *mut crate::leanh::LeanObject,
    mut v_a_1972_: *mut crate::leanh::LeanObject,
    mut v_a_1973_: *mut crate::leanh::LeanObject,
    mut v_a_1974_: *mut crate::leanh::LeanObject,
    mut v_a_1975_: *mut crate::leanh::LeanObject,
    mut v_a_1976_: *mut crate::leanh::LeanObject,
    mut v_a_1977_: *mut crate::leanh::LeanObject,
    mut v_a_1978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1979_ = l_Int_Linear_Poly_isNonlinear(
        v_p_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_,
        v_a_1975_, v_a_1976_, v_a_1977_,
    );
    crate::leanh::lean_dec(v_a_1977_);
    crate::leanh::lean_dec_ref(v_a_1976_);
    crate::leanh::lean_dec(v_a_1975_);
    crate::leanh::lean_dec_ref(v_a_1974_);
    crate::leanh::lean_dec(v_a_1973_);
    crate::leanh::lean_dec_ref(v_a_1972_);
    crate::leanh::lean_dec(v_a_1971_);
    crate::leanh::lean_dec_ref(v_a_1970_);
    crate::leanh::lean_dec(v_a_1969_);
    crate::leanh::lean_dec(v_a_1968_);
    crate::leanh::lean_dec_ref(v_p_1967_);
    return v_res_1979_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___redArg(
    mut v_a_1980_: *mut crate::leanh::LeanObject,
    mut v_a_1981_: *mut crate::leanh::LeanObject,
    mut v_a_1982_: *mut crate::leanh::LeanObject,
    mut v_a_1983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1987_: u8 = 0;
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut v_unused_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: u8 = 0;
    let mut v_a_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2009_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1980_) == 0 {
                    v_isSharedCheck_1991_ = (!crate::leanh::lean_is_exclusive(v_a_1980_)) as u8;
                    if v_isSharedCheck_1991_ == 0 {
                        v_unused_1992_ = crate::leanh::lean_ctor_get(v_a_1980_, 0);
                        crate::leanh::lean_dec(v_unused_1992_);
                        v___x_1986_ = v_a_1980_;
                        v_isShared_1987_ = v_isSharedCheck_1991_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_1980_);
                        v___x_1986_ = crate::leanh::lean_box(0);
                        v_isShared_1987_ = v_isSharedCheck_1991_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_v_1993_ = crate::leanh::lean_ctor_get(v_a_1980_, 1);
                    crate::leanh::lean_inc(v_v_1993_);
                    v_p_1994_ = crate::leanh::lean_ctor_get(v_a_1980_, 2);
                    crate::leanh::lean_inc_ref(v_p_1994_);
                    crate::leanh::lean_dec_ref_known(v_a_1980_, 3);
                    v___x_1995_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(
                        v_v_1993_, v_a_1982_, v_a_1983_,
                    );
                    crate::leanh::lean_dec(v_v_1993_);
                    if crate::leanh::lean_obj_tag(v___x_1995_) == 0 {
                        v_a_1996_ = crate::leanh::lean_ctor_get(v___x_1995_, 0);
                        crate::leanh::lean_inc(v_a_1996_);
                        crate::leanh::lean_dec_ref_known(v___x_1995_, 1);
                        v___x_1997_ =
                            l_Lean_Meta_Grind_getGeneration___redArg(v_a_1996_, v_a_1982_);
                        crate::leanh::lean_dec(v_a_1996_);
                        if crate::leanh::lean_obj_tag(v___x_1997_) == 0 {
                            v_a_1998_ = crate::leanh::lean_ctor_get(v___x_1997_, 0);
                            crate::leanh::lean_inc(v_a_1998_);
                            crate::leanh::lean_dec_ref_known(v___x_1997_, 1);
                            v___x_1999_ = lean_nat_dec_le(v_a_1998_, v_a_1981_);
                            if v___x_1999_ == 0 {
                                crate::leanh::lean_dec(v_a_1981_);
                                v_a_1980_ = v_p_1994_;
                                v_a_1981_ = v_a_1998_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_1998_);
                                v_a_1980_ = v_p_1994_;
                                state = 0;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_p_1994_);
                            crate::leanh::lean_dec(v_a_1981_);
                            return v___x_1997_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_p_1994_);
                        crate::leanh::lean_dec(v_a_1981_);
                        v_a_2002_ = crate::leanh::lean_ctor_get(v___x_1995_, 0);
                        v_isSharedCheck_2009_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1995_)) as u8;
                        if v_isSharedCheck_2009_ == 0 {
                            v___x_2004_ = v___x_1995_;
                            v_isShared_2005_ = v_isSharedCheck_2009_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2002_);
                            crate::leanh::lean_dec(v___x_1995_);
                            v___x_2004_ = crate::leanh::lean_box(0);
                            v_isShared_2005_ = v_isSharedCheck_2009_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1987_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1986_, 0, v_a_1981_);
                    v___x_1989_ = v___x_1986_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1990_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1981_);
                    v___x_1989_ = v_reuseFailAlloc_1990_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1989_;
            }
            3 => {
                if v_isShared_2005_ == 0 {
                    v___x_2007_ = v___x_2004_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2008_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
                    v___x_2007_ = v_reuseFailAlloc_2008_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2007_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___redArg___boxed(
    mut v_a_2010_: *mut crate::leanh::LeanObject,
    mut v_a_2011_: *mut crate::leanh::LeanObject,
    mut v_a_2012_: *mut crate::leanh::LeanObject,
    mut v_a_2013_: *mut crate::leanh::LeanObject,
    mut v_a_2014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2015_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___redArg(v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
    crate::leanh::lean_dec_ref(v_a_2013_);
    crate::leanh::lean_dec(v_a_2012_);
    return v_res_2015_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go(
    mut v_a_2016_: *mut crate::leanh::LeanObject,
    mut v_a_2017_: *mut crate::leanh::LeanObject,
    mut v_a_2018_: *mut crate::leanh::LeanObject,
    mut v_a_2019_: *mut crate::leanh::LeanObject,
    mut v_a_2020_: *mut crate::leanh::LeanObject,
    mut v_a_2021_: *mut crate::leanh::LeanObject,
    mut v_a_2022_: *mut crate::leanh::LeanObject,
    mut v_a_2023_: *mut crate::leanh::LeanObject,
    mut v_a_2024_: *mut crate::leanh::LeanObject,
    mut v_a_2025_: *mut crate::leanh::LeanObject,
    mut v_a_2026_: *mut crate::leanh::LeanObject,
    mut v_a_2027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2029_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___redArg(v_a_2016_, v_a_2017_, v_a_2018_, v_a_2026_);
    return v___x_2029_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___boxed(
    mut v_a_2030_: *mut crate::leanh::LeanObject,
    mut v_a_2031_: *mut crate::leanh::LeanObject,
    mut v_a_2032_: *mut crate::leanh::LeanObject,
    mut v_a_2033_: *mut crate::leanh::LeanObject,
    mut v_a_2034_: *mut crate::leanh::LeanObject,
    mut v_a_2035_: *mut crate::leanh::LeanObject,
    mut v_a_2036_: *mut crate::leanh::LeanObject,
    mut v_a_2037_: *mut crate::leanh::LeanObject,
    mut v_a_2038_: *mut crate::leanh::LeanObject,
    mut v_a_2039_: *mut crate::leanh::LeanObject,
    mut v_a_2040_: *mut crate::leanh::LeanObject,
    mut v_a_2041_: *mut crate::leanh::LeanObject,
    mut v_a_2042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2043_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go(v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
    crate::leanh::lean_dec(v_a_2041_);
    crate::leanh::lean_dec_ref(v_a_2040_);
    crate::leanh::lean_dec(v_a_2039_);
    crate::leanh::lean_dec_ref(v_a_2038_);
    crate::leanh::lean_dec(v_a_2037_);
    crate::leanh::lean_dec_ref(v_a_2036_);
    crate::leanh::lean_dec(v_a_2035_);
    crate::leanh::lean_dec_ref(v_a_2034_);
    crate::leanh::lean_dec(v_a_2033_);
    crate::leanh::lean_dec(v_a_2032_);
    return v_res_2043_;
}
pub unsafe fn l_Int_Linear_Poly_getGeneration___redArg(
    mut v_p_2044_: *mut crate::leanh::LeanObject,
    mut v_a_2045_: *mut crate::leanh::LeanObject,
    mut v_a_2046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2048_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2049_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___redArg(v_p_2044_, v___x_2048_, v_a_2045_, v_a_2046_);
    return v___x_2049_;
}
pub unsafe fn l_Int_Linear_Poly_getGeneration___redArg___boxed(
    mut v_p_2050_: *mut crate::leanh::LeanObject,
    mut v_a_2051_: *mut crate::leanh::LeanObject,
    mut v_a_2052_: *mut crate::leanh::LeanObject,
    mut v_a_2053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2054_ = l_Int_Linear_Poly_getGeneration___redArg(v_p_2050_, v_a_2051_, v_a_2052_);
    crate::leanh::lean_dec_ref(v_a_2052_);
    crate::leanh::lean_dec(v_a_2051_);
    return v_res_2054_;
}
pub unsafe fn l_Int_Linear_Poly_getGeneration(
    mut v_p_2055_: *mut crate::leanh::LeanObject,
    mut v_a_2056_: *mut crate::leanh::LeanObject,
    mut v_a_2057_: *mut crate::leanh::LeanObject,
    mut v_a_2058_: *mut crate::leanh::LeanObject,
    mut v_a_2059_: *mut crate::leanh::LeanObject,
    mut v_a_2060_: *mut crate::leanh::LeanObject,
    mut v_a_2061_: *mut crate::leanh::LeanObject,
    mut v_a_2062_: *mut crate::leanh::LeanObject,
    mut v_a_2063_: *mut crate::leanh::LeanObject,
    mut v_a_2064_: *mut crate::leanh::LeanObject,
    mut v_a_2065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2067_ = l_Int_Linear_Poly_getGeneration___redArg(v_p_2055_, v_a_2056_, v_a_2064_);
    return v___x_2067_;
}
pub unsafe fn l_Int_Linear_Poly_getGeneration___boxed(
    mut v_p_2068_: *mut crate::leanh::LeanObject,
    mut v_a_2069_: *mut crate::leanh::LeanObject,
    mut v_a_2070_: *mut crate::leanh::LeanObject,
    mut v_a_2071_: *mut crate::leanh::LeanObject,
    mut v_a_2072_: *mut crate::leanh::LeanObject,
    mut v_a_2073_: *mut crate::leanh::LeanObject,
    mut v_a_2074_: *mut crate::leanh::LeanObject,
    mut v_a_2075_: *mut crate::leanh::LeanObject,
    mut v_a_2076_: *mut crate::leanh::LeanObject,
    mut v_a_2077_: *mut crate::leanh::LeanObject,
    mut v_a_2078_: *mut crate::leanh::LeanObject,
    mut v_a_2079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2080_ = l_Int_Linear_Poly_getGeneration(
        v_p_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_,
        v_a_2076_, v_a_2077_, v_a_2078_,
    );
    crate::leanh::lean_dec(v_a_2078_);
    crate::leanh::lean_dec_ref(v_a_2077_);
    crate::leanh::lean_dec(v_a_2076_);
    crate::leanh::lean_dec_ref(v_a_2075_);
    crate::leanh::lean_dec(v_a_2074_);
    crate::leanh::lean_dec_ref(v_a_2073_);
    crate::leanh::lean_dec(v_a_2072_);
    crate::leanh::lean_dec_ref(v_a_2071_);
    crate::leanh::lean_dec(v_a_2070_);
    crate::leanh::lean_dec(v_a_2069_);
    return v_res_2080_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(
    mut v_a_2081_: *mut crate::leanh::LeanObject,
    mut v_a_2082_: *mut crate::leanh::LeanObject,
    mut v_a_2083_: *mut crate::leanh::LeanObject,
    mut v_a_2084_: *mut crate::leanh::LeanObject,
    mut v_a_2085_: *mut crate::leanh::LeanObject,
    mut v_a_2086_: *mut crate::leanh::LeanObject,
    mut v_a_2087_: *mut crate::leanh::LeanObject,
    mut v_a_2088_: *mut crate::leanh::LeanObject,
    mut v_a_2089_: *mut crate::leanh::LeanObject,
    mut v_a_2090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2098_: u8 = 0;
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2102_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2092_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2085_);
                if crate::leanh::lean_obj_tag(v___x_2092_) == 0 {
                    v_a_2093_ = crate::leanh::lean_ctor_get(v___x_2092_, 0);
                    crate::leanh::lean_inc(v_a_2093_);
                    crate::leanh::lean_dec_ref_known(v___x_2092_, 1);
                    v___x_2094_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(
                        v_a_2093_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_,
                        v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_,
                    );
                    return v___x_2094_;
                } else {
                    v_a_2095_ = crate::leanh::lean_ctor_get(v___x_2092_, 0);
                    v_isSharedCheck_2102_ = (!crate::leanh::lean_is_exclusive(v___x_2092_)) as u8;
                    if v_isSharedCheck_2102_ == 0 {
                        v___x_2097_ = v___x_2092_;
                        v_isShared_2098_ = v_isSharedCheck_2102_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2095_);
                        crate::leanh::lean_dec(v___x_2092_);
                        v___x_2097_ = crate::leanh::lean_box(0);
                        v_isShared_2098_ = v_isSharedCheck_2102_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2098_ == 0 {
                    v___x_2100_ = v___x_2097_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2101_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
                    v___x_2100_ = v_reuseFailAlloc_2101_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2100_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f___boxed(
    mut v_a_2103_: *mut crate::leanh::LeanObject,
    mut v_a_2104_: *mut crate::leanh::LeanObject,
    mut v_a_2105_: *mut crate::leanh::LeanObject,
    mut v_a_2106_: *mut crate::leanh::LeanObject,
    mut v_a_2107_: *mut crate::leanh::LeanObject,
    mut v_a_2108_: *mut crate::leanh::LeanObject,
    mut v_a_2109_: *mut crate::leanh::LeanObject,
    mut v_a_2110_: *mut crate::leanh::LeanObject,
    mut v_a_2111_: *mut crate::leanh::LeanObject,
    mut v_a_2112_: *mut crate::leanh::LeanObject,
    mut v_a_2113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2114_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(
        v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_,
        v_a_2111_, v_a_2112_,
    );
    crate::leanh::lean_dec(v_a_2112_);
    crate::leanh::lean_dec_ref(v_a_2111_);
    crate::leanh::lean_dec(v_a_2110_);
    crate::leanh::lean_dec_ref(v_a_2109_);
    crate::leanh::lean_dec(v_a_2108_);
    crate::leanh::lean_dec_ref(v_a_2107_);
    crate::leanh::lean_dec(v_a_2106_);
    crate::leanh::lean_dec_ref(v_a_2105_);
    crate::leanh::lean_dec(v_a_2104_);
    crate::leanh::lean_dec(v_a_2103_);
    return v_res_2114_;
}
pub unsafe fn l_Int_Linear_Poly_normCommRing_x3f___lam__0(
    mut v_a_2115_: u8,
    mut v_s_2116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vars_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_x27_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_x27_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natDef_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dvds_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lowers_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uppers_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimStack_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_occurs_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextCnstrId_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_2132_: u8 = 0;
    let mut v_conflict_x3f_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_divMod_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntIds_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntInfos_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nonlinearOccs_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2143_: u8 = 0;
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2147_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_2117_ = crate::leanh::lean_ctor_get(v_s_2116_, 0);
                v_varMap_2118_ = crate::leanh::lean_ctor_get(v_s_2116_, 1);
                v_vars_x27_2119_ = crate::leanh::lean_ctor_get(v_s_2116_, 2);
                v_varMap_x27_2120_ = crate::leanh::lean_ctor_get(v_s_2116_, 3);
                v_natToIntMap_2121_ = crate::leanh::lean_ctor_get(v_s_2116_, 4);
                v_natDef_2122_ = crate::leanh::lean_ctor_get(v_s_2116_, 5);
                v_dvds_2123_ = crate::leanh::lean_ctor_get(v_s_2116_, 6);
                v_lowers_2124_ = crate::leanh::lean_ctor_get(v_s_2116_, 7);
                v_uppers_2125_ = crate::leanh::lean_ctor_get(v_s_2116_, 8);
                v_diseqs_2126_ = crate::leanh::lean_ctor_get(v_s_2116_, 9);
                v_elimEqs_2127_ = crate::leanh::lean_ctor_get(v_s_2116_, 10);
                v_elimStack_2128_ = crate::leanh::lean_ctor_get(v_s_2116_, 11);
                v_occurs_2129_ = crate::leanh::lean_ctor_get(v_s_2116_, 12);
                v_assignment_2130_ = crate::leanh::lean_ctor_get(v_s_2116_, 13);
                v_nextCnstrId_2131_ = crate::leanh::lean_ctor_get(v_s_2116_, 14);
                v_caseSplits_2132_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2116_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23) as u32,
                );
                v_conflict_x3f_2133_ = crate::leanh::lean_ctor_get(v_s_2116_, 15);
                v_diseqSplits_2134_ = crate::leanh::lean_ctor_get(v_s_2116_, 16);
                v_divMod_2135_ = crate::leanh::lean_ctor_get(v_s_2116_, 17);
                v_toIntIds_2136_ = crate::leanh::lean_ctor_get(v_s_2116_, 18);
                v_toIntInfos_2137_ = crate::leanh::lean_ctor_get(v_s_2116_, 19);
                v_toIntTermMap_2138_ = crate::leanh::lean_ctor_get(v_s_2116_, 20);
                v_toIntVarMap_2139_ = crate::leanh::lean_ctor_get(v_s_2116_, 21);
                v_nonlinearOccs_2140_ = crate::leanh::lean_ctor_get(v_s_2116_, 22);
                v_isSharedCheck_2147_ = (!crate::leanh::lean_is_exclusive(v_s_2116_)) as u8;
                if v_isSharedCheck_2147_ == 0 {
                    v___x_2142_ = v_s_2116_;
                    v_isShared_2143_ = v_isSharedCheck_2147_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nonlinearOccs_2140_);
                    crate::leanh::lean_inc(v_toIntVarMap_2139_);
                    crate::leanh::lean_inc(v_toIntTermMap_2138_);
                    crate::leanh::lean_inc(v_toIntInfos_2137_);
                    crate::leanh::lean_inc(v_toIntIds_2136_);
                    crate::leanh::lean_inc(v_divMod_2135_);
                    crate::leanh::lean_inc(v_diseqSplits_2134_);
                    crate::leanh::lean_inc(v_conflict_x3f_2133_);
                    crate::leanh::lean_inc(v_nextCnstrId_2131_);
                    crate::leanh::lean_inc(v_assignment_2130_);
                    crate::leanh::lean_inc(v_occurs_2129_);
                    crate::leanh::lean_inc(v_elimStack_2128_);
                    crate::leanh::lean_inc(v_elimEqs_2127_);
                    crate::leanh::lean_inc(v_diseqs_2126_);
                    crate::leanh::lean_inc(v_uppers_2125_);
                    crate::leanh::lean_inc(v_lowers_2124_);
                    crate::leanh::lean_inc(v_dvds_2123_);
                    crate::leanh::lean_inc(v_natDef_2122_);
                    crate::leanh::lean_inc(v_natToIntMap_2121_);
                    crate::leanh::lean_inc(v_varMap_x27_2120_);
                    crate::leanh::lean_inc(v_vars_x27_2119_);
                    crate::leanh::lean_inc(v_varMap_2118_);
                    crate::leanh::lean_inc(v_vars_2117_);
                    crate::leanh::lean_dec(v_s_2116_);
                    v___x_2142_ = crate::leanh::lean_box(0);
                    v_isShared_2143_ = v_isSharedCheck_2147_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2143_ == 0 {
                    v___x_2145_ = v___x_2142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2146_ = crate::leanh::lean_alloc_ctor(0, 23, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_vars_2117_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_varMap_2118_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 2, v_vars_x27_2119_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 3, v_varMap_x27_2120_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 4, v_natToIntMap_2121_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 5, v_natDef_2122_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 6, v_dvds_2123_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 7, v_lowers_2124_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 8, v_uppers_2125_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 9, v_diseqs_2126_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 10, v_elimEqs_2127_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 11, v_elimStack_2128_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 12, v_occurs_2129_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 13, v_assignment_2130_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 14, v_nextCnstrId_2131_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 15, v_conflict_x3f_2133_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 16, v_diseqSplits_2134_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 17, v_divMod_2135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 18, v_toIntIds_2136_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 19, v_toIntInfos_2137_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 20, v_toIntTermMap_2138_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 21, v_toIntVarMap_2139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 22, v_nonlinearOccs_2140_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2146_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23) as u32,
                        v_caseSplits_2132_,
                    );
                    v___x_2145_ = v_reuseFailAlloc_2146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2145_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23 + 1) as u32,
                    v_a_2115_,
                );
                return v___x_2145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_normCommRing_x3f___lam__0___boxed(
    mut v_a_2148_: *mut crate::leanh::LeanObject,
    mut v_s_2149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_152961__boxed_2150_: u8 = 0;
    let mut v_res_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_152961__boxed_2150_ = (crate::leanh::lean_unbox(v_a_2148_) as u8);
    v_res_2151_ = l_Int_Linear_Poly_normCommRing_x3f___lam__0(v_a_152961__boxed_2150_, v_s_2149_);
    return v_res_2151_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0(
    mut v_a_2152_: *mut crate::leanh::LeanObject,
    mut v_s_2153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_2168_: u8 = 0;
    let mut v_invSet_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_2172_: u8 = 0;
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v_id_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2194_: u8 = 0;
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2202_: u8 = 0;
    let mut v_unused_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2204_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2154_ = crate::leanh::lean_ctor_get(v_s_2153_, 0);
                v_invFn_x3f_2155_ = crate::leanh::lean_ctor_get(v_s_2153_, 1);
                v_semiringId_x3f_2156_ = crate::leanh::lean_ctor_get(v_s_2153_, 2);
                v_commSemiringInst_2157_ = crate::leanh::lean_ctor_get(v_s_2153_, 3);
                v_commRingInst_2158_ = crate::leanh::lean_ctor_get(v_s_2153_, 4);
                v_noZeroDivInst_x3f_2159_ = crate::leanh::lean_ctor_get(v_s_2153_, 5);
                v_fieldInst_x3f_2160_ = crate::leanh::lean_ctor_get(v_s_2153_, 6);
                v_powIdentityInst_x3f_2161_ = crate::leanh::lean_ctor_get(v_s_2153_, 7);
                v_denoteEntries_2162_ = crate::leanh::lean_ctor_get(v_s_2153_, 8);
                v_nextId_2163_ = crate::leanh::lean_ctor_get(v_s_2153_, 9);
                v_steps_2164_ = crate::leanh::lean_ctor_get(v_s_2153_, 10);
                v_queue_2165_ = crate::leanh::lean_ctor_get(v_s_2153_, 11);
                v_basis_2166_ = crate::leanh::lean_ctor_get(v_s_2153_, 12);
                v_diseqs_2167_ = crate::leanh::lean_ctor_get(v_s_2153_, 13);
                v_recheck_2168_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2153_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_2169_ = crate::leanh::lean_ctor_get(v_s_2153_, 14);
                v_powIdentityVarCount_2170_ = crate::leanh::lean_ctor_get(v_s_2153_, 15);
                v_numEq0_x3f_2171_ = crate::leanh::lean_ctor_get(v_s_2153_, 16);
                v_numEq0Updated_2172_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2153_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_2204_ = (!crate::leanh::lean_is_exclusive(v_s_2153_)) as u8;
                if v_isSharedCheck_2204_ == 0 {
                    v___x_2174_ = v_s_2153_;
                    v_isShared_2175_ = v_isSharedCheck_2204_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numEq0_x3f_2171_);
                    crate::leanh::lean_inc(v_powIdentityVarCount_2170_);
                    crate::leanh::lean_inc(v_invSet_2169_);
                    crate::leanh::lean_inc(v_diseqs_2167_);
                    crate::leanh::lean_inc(v_basis_2166_);
                    crate::leanh::lean_inc(v_queue_2165_);
                    crate::leanh::lean_inc(v_steps_2164_);
                    crate::leanh::lean_inc(v_nextId_2163_);
                    crate::leanh::lean_inc(v_denoteEntries_2162_);
                    crate::leanh::lean_inc(v_powIdentityInst_x3f_2161_);
                    crate::leanh::lean_inc(v_fieldInst_x3f_2160_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_2159_);
                    crate::leanh::lean_inc(v_commRingInst_2158_);
                    crate::leanh::lean_inc(v_commSemiringInst_2157_);
                    crate::leanh::lean_inc(v_semiringId_x3f_2156_);
                    crate::leanh::lean_inc(v_invFn_x3f_2155_);
                    crate::leanh::lean_inc(v_toRing_2154_);
                    crate::leanh::lean_dec(v_s_2153_);
                    v___x_2174_ = crate::leanh::lean_box(0);
                    v_isShared_2175_ = v_isSharedCheck_2204_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_2176_ = crate::leanh::lean_ctor_get(v_toRing_2154_, 0);
                v_type_2177_ = crate::leanh::lean_ctor_get(v_toRing_2154_, 1);
                v_u_2178_ = crate::leanh::lean_ctor_get(v_toRing_2154_, 2);
                v_ringInst_2179_ = crate::leanh::lean_ctor_get(v_toRing_2154_, 3);
                v_semiringInst_2180_ = crate::leanh::lean_ctor_get(v_toRing_2154_, 4);
                v_charInst_x3f_2181_ = crate::leanh::lean_ctor_get(v_toRing_2154_, 5);
                v_addFn_x3f_2182_ = crate::leanh::lean_ctor_get(v_toRing_2154_, 6);
                v_mulFn_x3f_2183_ = crate::leanh::lean_ctor_get(v_toRing_2154_, 7);
                v_subFn_x3f_2184_ = crate::leanh::lean_ctor_get(v_toRing_2154_, 8);
                v_powFn_x3f_2185_ = crate::leanh::lean_ctor_get(v_toRing_2154_, 10);
                v_intCastFn_x3f_2186_ = crate::leanh::lean_ctor_get(v_toRing_2154_, 11);
                v_natCastFn_x3f_2187_ = crate::leanh::lean_ctor_get(v_toRing_2154_, 12);
                v_one_x3f_2188_ = crate::leanh::lean_ctor_get(v_toRing_2154_, 13);
                v_vars_2189_ = crate::leanh::lean_ctor_get(v_toRing_2154_, 14);
                v_varMap_2190_ = crate::leanh::lean_ctor_get(v_toRing_2154_, 15);
                v_denote_2191_ = crate::leanh::lean_ctor_get(v_toRing_2154_, 16);
                v_isSharedCheck_2202_ = (!crate::leanh::lean_is_exclusive(v_toRing_2154_)) as u8;
                if v_isSharedCheck_2202_ == 0 {
                    v_unused_2203_ = crate::leanh::lean_ctor_get(v_toRing_2154_, 9);
                    crate::leanh::lean_dec(v_unused_2203_);
                    v___x_2193_ = v_toRing_2154_;
                    v_isShared_2194_ = v_isSharedCheck_2202_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_2191_);
                    crate::leanh::lean_inc(v_varMap_2190_);
                    crate::leanh::lean_inc(v_vars_2189_);
                    crate::leanh::lean_inc(v_one_x3f_2188_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_2187_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_2186_);
                    crate::leanh::lean_inc(v_powFn_x3f_2185_);
                    crate::leanh::lean_inc(v_subFn_x3f_2184_);
                    crate::leanh::lean_inc(v_mulFn_x3f_2183_);
                    crate::leanh::lean_inc(v_addFn_x3f_2182_);
                    crate::leanh::lean_inc(v_charInst_x3f_2181_);
                    crate::leanh::lean_inc(v_semiringInst_2180_);
                    crate::leanh::lean_inc(v_ringInst_2179_);
                    crate::leanh::lean_inc(v_u_2178_);
                    crate::leanh::lean_inc(v_type_2177_);
                    crate::leanh::lean_inc(v_id_2176_);
                    crate::leanh::lean_dec(v_toRing_2154_);
                    v___x_2193_ = crate::leanh::lean_box(0);
                    v_isShared_2194_ = v_isSharedCheck_2202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2195_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2195_, 0, v_a_2152_);
                if v_isShared_2194_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2193_, 9, v___x_2195_);
                    v___x_2197_ = v___x_2193_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2201_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_id_2176_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_type_2177_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 2, v_u_2178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 3, v_ringInst_2179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 4, v_semiringInst_2180_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 5, v_charInst_x3f_2181_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 6, v_addFn_x3f_2182_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 7, v_mulFn_x3f_2183_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 8, v_subFn_x3f_2184_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 9, v___x_2195_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 10, v_powFn_x3f_2185_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 11, v_intCastFn_x3f_2186_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 12, v_natCastFn_x3f_2187_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 13, v_one_x3f_2188_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 14, v_vars_2189_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 15, v_varMap_2190_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 16, v_denote_2191_);
                    v___x_2197_ = v_reuseFailAlloc_2201_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2175_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2174_, 0, v___x_2197_);
                    v___x_2199_ = v___x_2174_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2200_ = crate::leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_invFn_x3f_2155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 2, v_semiringId_x3f_2156_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2200_,
                        3,
                        v_commSemiringInst_2157_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 4, v_commRingInst_2158_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2200_,
                        5,
                        v_noZeroDivInst_x3f_2159_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 6, v_fieldInst_x3f_2160_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2200_,
                        7,
                        v_powIdentityInst_x3f_2161_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 8, v_denoteEntries_2162_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 9, v_nextId_2163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 10, v_steps_2164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 11, v_queue_2165_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 12, v_basis_2166_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 13, v_diseqs_2167_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 14, v_invSet_2169_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2200_,
                        15,
                        v_powIdentityVarCount_2170_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 16, v_numEq0_x3f_2171_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2200_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_recheck_2168_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2200_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_2172_,
                    );
                    v___x_2199_ = v_reuseFailAlloc_2200_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2199_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1_spec__4(
    mut v_msgData_2205_: *mut crate::leanh::LeanObject,
    mut v___y_2206_: *mut crate::leanh::LeanObject,
    mut v___y_2207_: *mut crate::leanh::LeanObject,
    mut v___y_2208_: *mut crate::leanh::LeanObject,
    mut v___y_2209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2211_ = lean_st_ref_get(v___y_2209_);
    v_env_2212_ = crate::leanh::lean_ctor_get(v___x_2211_, 0);
    crate::leanh::lean_inc_ref(v_env_2212_);
    crate::leanh::lean_dec(v___x_2211_);
    v___x_2213_ = lean_st_ref_get(v___y_2207_);
    v_mctx_2214_ = crate::leanh::lean_ctor_get(v___x_2213_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2214_);
    crate::leanh::lean_dec(v___x_2213_);
    v_lctx_2215_ = crate::leanh::lean_ctor_get(v___y_2206_, 2);
    v_options_2216_ = crate::leanh::lean_ctor_get(v___y_2208_, 2);
    crate::leanh::lean_inc_ref(v_options_2216_);
    crate::leanh::lean_inc_ref(v_lctx_2215_);
    v___x_2217_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2217_, 0, v_env_2212_);
    crate::leanh::lean_ctor_set(v___x_2217_, 1, v_mctx_2214_);
    crate::leanh::lean_ctor_set(v___x_2217_, 2, v_lctx_2215_);
    crate::leanh::lean_ctor_set(v___x_2217_, 3, v_options_2216_);
    v___x_2218_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2218_, 0, v___x_2217_);
    crate::leanh::lean_ctor_set(v___x_2218_, 1, v_msgData_2205_);
    v___x_2219_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2219_, 0, v___x_2218_);
    return v___x_2219_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1_spec__4___boxed(
    mut v_msgData_2220_: *mut crate::leanh::LeanObject,
    mut v___y_2221_: *mut crate::leanh::LeanObject,
    mut v___y_2222_: *mut crate::leanh::LeanObject,
    mut v___y_2223_: *mut crate::leanh::LeanObject,
    mut v___y_2224_: *mut crate::leanh::LeanObject,
    mut v___y_2225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2226_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msgData_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
    crate::leanh::lean_dec(v___y_2224_);
    crate::leanh::lean_dec_ref(v___y_2223_);
    crate::leanh::lean_dec(v___y_2222_);
    crate::leanh::lean_dec_ref(v___y_2221_);
    return v_res_2226_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(
    mut v_msg_2227_: *mut crate::leanh::LeanObject,
    mut v___y_2228_: *mut crate::leanh::LeanObject,
    mut v___y_2229_: *mut crate::leanh::LeanObject,
    mut v___y_2230_: *mut crate::leanh::LeanObject,
    mut v___y_2231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2238_: u8 = 0;
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2243_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2233_ = crate::leanh::lean_ctor_get(v___y_2230_, 5);
                v___x_2234_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
                v_a_2235_ = crate::leanh::lean_ctor_get(v___x_2234_, 0);
                v_isSharedCheck_2243_ = (!crate::leanh::lean_is_exclusive(v___x_2234_)) as u8;
                if v_isSharedCheck_2243_ == 0 {
                    v___x_2237_ = v___x_2234_;
                    v_isShared_2238_ = v_isSharedCheck_2243_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2235_);
                    crate::leanh::lean_dec(v___x_2234_);
                    v___x_2237_ = crate::leanh::lean_box(0);
                    v_isShared_2238_ = v_isSharedCheck_2243_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2233_);
                v___x_2239_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2239_, 0, v_ref_2233_);
                crate::leanh::lean_ctor_set(v___x_2239_, 1, v_a_2235_);
                if v_isShared_2238_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2237_, 1);
                    crate::leanh::lean_ctor_set(v___x_2237_, 0, v___x_2239_);
                    v___x_2241_ = v___x_2237_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2242_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2239_);
                    v___x_2241_ = v_reuseFailAlloc_2242_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2241_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg___boxed(
    mut v_msg_2244_: *mut crate::leanh::LeanObject,
    mut v___y_2245_: *mut crate::leanh::LeanObject,
    mut v___y_2246_: *mut crate::leanh::LeanObject,
    mut v___y_2247_: *mut crate::leanh::LeanObject,
    mut v___y_2248_: *mut crate::leanh::LeanObject,
    mut v___y_2249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2250_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
    crate::leanh::lean_dec(v___y_2248_);
    crate::leanh::lean_dec_ref(v___y_2247_);
    crate::leanh::lean_dec(v___y_2246_);
    crate::leanh::lean_dec_ref(v___y_2245_);
    return v_res_2250_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2252_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0;
    v___x_2253_ = l_Lean_stringToMessageData(v___x_2252_);
    return v___x_2253_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(
    mut v_type_2254_: *mut crate::leanh::LeanObject,
    mut v___y_2255_: *mut crate::leanh::LeanObject,
    mut v___y_2256_: *mut crate::leanh::LeanObject,
    mut v___y_2257_: *mut crate::leanh::LeanObject,
    mut v___y_2258_: *mut crate::leanh::LeanObject,
    mut v___y_2259_: *mut crate::leanh::LeanObject,
    mut v___y_2260_: *mut crate::leanh::LeanObject,
    mut v___y_2261_: *mut crate::leanh::LeanObject,
    mut v___y_2262_: *mut crate::leanh::LeanObject,
    mut v___y_2263_: *mut crate::leanh::LeanObject,
    mut v___y_2264_: *mut crate::leanh::LeanObject,
    mut v___y_2265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2271_: u8 = 0;
    let mut v_val_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2280_: u8 = 0;
    let mut v_a_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2284_: u8 = 0;
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_type_2254_);
                v___x_2267_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v_type_2254_,
                    v___y_2262_,
                    v___y_2263_,
                    v___y_2264_,
                    v___y_2265_,
                );
                if crate::leanh::lean_obj_tag(v___x_2267_) == 0 {
                    v_a_2268_ = crate::leanh::lean_ctor_get(v___x_2267_, 0);
                    v_isSharedCheck_2280_ = (!crate::leanh::lean_is_exclusive(v___x_2267_)) as u8;
                    if v_isSharedCheck_2280_ == 0 {
                        v___x_2270_ = v___x_2267_;
                        v_isShared_2271_ = v_isSharedCheck_2280_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2268_);
                        crate::leanh::lean_dec(v___x_2267_);
                        v___x_2270_ = crate::leanh::lean_box(0);
                        v_isShared_2271_ = v_isSharedCheck_2280_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_2254_);
                    v_a_2281_ = crate::leanh::lean_ctor_get(v___x_2267_, 0);
                    v_isSharedCheck_2288_ = (!crate::leanh::lean_is_exclusive(v___x_2267_)) as u8;
                    if v_isSharedCheck_2288_ == 0 {
                        v___x_2283_ = v___x_2267_;
                        v_isShared_2284_ = v_isSharedCheck_2288_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2281_);
                        crate::leanh::lean_dec(v___x_2267_);
                        v___x_2283_ = crate::leanh::lean_box(0);
                        v_isShared_2284_ = v_isSharedCheck_2288_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2268_) == 1 {
                    crate::leanh::lean_dec_ref(v_type_2254_);
                    v_val_2272_ = crate::leanh::lean_ctor_get(v_a_2268_, 0);
                    crate::leanh::lean_inc(v_val_2272_);
                    crate::leanh::lean_dec_ref_known(v_a_2268_, 1);
                    if v_isShared_2271_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2270_, 0, v_val_2272_);
                        v___x_2274_ = v___x_2270_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2275_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_val_2272_);
                        v___x_2274_ = v_reuseFailAlloc_2275_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2270_);
                    crate::leanh::lean_dec(v_a_2268_);
                    v___x_2276_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1_once), _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1);
                    v___x_2277_ = l_Lean_indentExpr(v_type_2254_);
                    v___x_2278_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2278_, 0, v___x_2276_);
                    crate::leanh::lean_ctor_set(v___x_2278_, 1, v___x_2277_);
                    v___x_2279_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v___x_2278_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
                    return v___x_2279_;
                }
            }
            2 => {
                return v___x_2274_;
            }
            3 => {
                if v_isShared_2284_ == 0 {
                    v___x_2286_ = v___x_2283_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2287_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
                    v___x_2286_ = v_reuseFailAlloc_2287_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2286_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(
    mut v_type_2289_: *mut crate::leanh::LeanObject,
    mut v___y_2290_: *mut crate::leanh::LeanObject,
    mut v___y_2291_: *mut crate::leanh::LeanObject,
    mut v___y_2292_: *mut crate::leanh::LeanObject,
    mut v___y_2293_: *mut crate::leanh::LeanObject,
    mut v___y_2294_: *mut crate::leanh::LeanObject,
    mut v___y_2295_: *mut crate::leanh::LeanObject,
    mut v___y_2296_: *mut crate::leanh::LeanObject,
    mut v___y_2297_: *mut crate::leanh::LeanObject,
    mut v___y_2298_: *mut crate::leanh::LeanObject,
    mut v___y_2299_: *mut crate::leanh::LeanObject,
    mut v___y_2300_: *mut crate::leanh::LeanObject,
    mut v___y_2301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2302_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v_type_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
    crate::leanh::lean_dec(v___y_2300_);
    crate::leanh::lean_dec_ref(v___y_2299_);
    crate::leanh::lean_dec(v___y_2298_);
    crate::leanh::lean_dec_ref(v___y_2297_);
    crate::leanh::lean_dec(v___y_2296_);
    crate::leanh::lean_dec_ref(v___y_2295_);
    crate::leanh::lean_dec(v___y_2294_);
    crate::leanh::lean_dec_ref(v___y_2293_);
    crate::leanh::lean_dec(v___y_2292_);
    crate::leanh::lean_dec(v___y_2291_);
    crate::leanh::lean_dec_ref(v___y_2290_);
    return v_res_2302_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(
    mut v_type_2303_: *mut crate::leanh::LeanObject,
    mut v_u_2304_: *mut crate::leanh::LeanObject,
    mut v_instDeclName_2305_: *mut crate::leanh::LeanObject,
    mut v_declName_2306_: *mut crate::leanh::LeanObject,
    mut v_expectedInst_2307_: *mut crate::leanh::LeanObject,
    mut v___y_2308_: *mut crate::leanh::LeanObject,
    mut v___y_2309_: *mut crate::leanh::LeanObject,
    mut v___y_2310_: *mut crate::leanh::LeanObject,
    mut v___y_2311_: *mut crate::leanh::LeanObject,
    mut v___y_2312_: *mut crate::leanh::LeanObject,
    mut v___y_2313_: *mut crate::leanh::LeanObject,
    mut v___y_2314_: *mut crate::leanh::LeanObject,
    mut v___y_2315_: *mut crate::leanh::LeanObject,
    mut v___y_2316_: *mut crate::leanh::LeanObject,
    mut v___y_2317_: *mut crate::leanh::LeanObject,
    mut v___y_2318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2335_: u8 = 0;
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2339_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2320_ = crate::leanh::lean_box(0);
                v___x_2321_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2321_, 0, v_u_2304_);
                crate::leanh::lean_ctor_set(v___x_2321_, 1, v___x_2320_);
                crate::leanh::lean_inc_ref(v___x_2321_);
                v___x_2322_ = l_Lean_mkConst(v_instDeclName_2305_, v___x_2321_);
                crate::leanh::lean_inc_ref(v_type_2303_);
                v___x_2323_ = l_Lean_Expr_app___override(v___x_2322_, v_type_2303_);
                v___x_2324_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_2323_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
                if crate::leanh::lean_obj_tag(v___x_2324_) == 0 {
                    v_a_2325_ = crate::leanh::lean_ctor_get(v___x_2324_, 0);
                    crate::leanh::lean_inc_n(v_a_2325_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2324_, 1);
                    crate::leanh::lean_inc(v_declName_2306_);
                    v___x_2326_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
                        v_declName_2306_,
                        v_a_2325_,
                        v_expectedInst_2307_,
                        v___y_2315_,
                        v___y_2316_,
                        v___y_2317_,
                        v___y_2318_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2326_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2326_, 1);
                        v___x_2327_ = l_Lean_mkConst(v_declName_2306_, v___x_2321_);
                        v___x_2328_ = l_Lean_mkAppB(v___x_2327_, v_type_2303_, v_a_2325_);
                        v___x_2329_ = l_Lean_Meta_Sym_canon(
                            v___x_2328_,
                            v___y_2313_,
                            v___y_2314_,
                            v___y_2315_,
                            v___y_2316_,
                            v___y_2317_,
                            v___y_2318_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2329_) == 0 {
                            v_a_2330_ = crate::leanh::lean_ctor_get(v___x_2329_, 0);
                            crate::leanh::lean_inc(v_a_2330_);
                            crate::leanh::lean_dec_ref_known(v___x_2329_, 1);
                            v___x_2331_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_2330_, v___y_2314_);
                            return v___x_2331_;
                        } else {
                            return v___x_2329_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2325_);
                        crate::leanh::lean_dec_ref_known(v___x_2321_, 2);
                        crate::leanh::lean_dec(v_declName_2306_);
                        crate::leanh::lean_dec_ref(v_type_2303_);
                        v_a_2332_ = crate::leanh::lean_ctor_get(v___x_2326_, 0);
                        v_isSharedCheck_2339_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2326_)) as u8;
                        if v_isSharedCheck_2339_ == 0 {
                            v___x_2334_ = v___x_2326_;
                            v_isShared_2335_ = v_isSharedCheck_2339_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2332_);
                            crate::leanh::lean_dec(v___x_2326_);
                            v___x_2334_ = crate::leanh::lean_box(0);
                            v_isShared_2335_ = v_isSharedCheck_2339_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2321_, 2);
                    crate::leanh::lean_dec_ref(v_expectedInst_2307_);
                    crate::leanh::lean_dec(v_declName_2306_);
                    crate::leanh::lean_dec_ref(v_type_2303_);
                    return v___x_2324_;
                }
            }
            1 => {
                if v_isShared_2335_ == 0 {
                    v___x_2337_ = v___x_2334_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2338_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
                    v___x_2337_ = v_reuseFailAlloc_2338_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2337_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_2340_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_u_2341_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_instDeclName_2342_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_declName_2343_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_expectedInst_2344_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_2345_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_2346_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_2347_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_2348_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_2349_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_2350_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_2351_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2352_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2353_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2354_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2355_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2356_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2357_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_2340_, v_u_2341_, v_instDeclName_2342_, v_declName_2343_, v_expectedInst_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
    crate::leanh::lean_dec(v___y_2355_);
    crate::leanh::lean_dec_ref(v___y_2354_);
    crate::leanh::lean_dec(v___y_2353_);
    crate::leanh::lean_dec_ref(v___y_2352_);
    crate::leanh::lean_dec(v___y_2351_);
    crate::leanh::lean_dec_ref(v___y_2350_);
    crate::leanh::lean_dec(v___y_2349_);
    crate::leanh::lean_dec_ref(v___y_2348_);
    crate::leanh::lean_dec(v___y_2347_);
    crate::leanh::lean_dec(v___y_2346_);
    crate::leanh::lean_dec_ref(v___y_2345_);
    return v_res_2357_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(
    mut v___y_2374_: *mut crate::leanh::LeanObject,
    mut v___y_2375_: *mut crate::leanh::LeanObject,
    mut v___y_2376_: *mut crate::leanh::LeanObject,
    mut v___y_2377_: *mut crate::leanh::LeanObject,
    mut v___y_2378_: *mut crate::leanh::LeanObject,
    mut v___y_2379_: *mut crate::leanh::LeanObject,
    mut v___y_2380_: *mut crate::leanh::LeanObject,
    mut v___y_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2390_: u8 = 0;
    let mut v_toRing_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedInst_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2413_: u8 = 0;
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2417_: u8 = 0;
    let mut v_unused_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2422_: u8 = 0;
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2426_: u8 = 0;
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut v_a_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2431_: u8 = 0;
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2386_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v___y_2374_,
                    v___y_2375_,
                    v___y_2376_,
                    v___y_2377_,
                    v___y_2378_,
                    v___y_2379_,
                    v___y_2380_,
                    v___y_2381_,
                    v___y_2382_,
                    v___y_2383_,
                    v___y_2384_,
                );
                if crate::leanh::lean_obj_tag(v___x_2386_) == 0 {
                    v_a_2387_ = crate::leanh::lean_ctor_get(v___x_2386_, 0);
                    v_isSharedCheck_2427_ = (!crate::leanh::lean_is_exclusive(v___x_2386_)) as u8;
                    if v_isSharedCheck_2427_ == 0 {
                        v___x_2389_ = v___x_2386_;
                        v_isShared_2390_ = v_isSharedCheck_2427_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2387_);
                        crate::leanh::lean_dec(v___x_2386_);
                        v___x_2389_ = crate::leanh::lean_box(0);
                        v_isShared_2390_ = v_isSharedCheck_2427_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2428_ = crate::leanh::lean_ctor_get(v___x_2386_, 0);
                    v_isSharedCheck_2435_ = (!crate::leanh::lean_is_exclusive(v___x_2386_)) as u8;
                    if v_isSharedCheck_2435_ == 0 {
                        v___x_2430_ = v___x_2386_;
                        v_isShared_2431_ = v_isSharedCheck_2435_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2428_);
                        crate::leanh::lean_dec(v___x_2386_);
                        v___x_2430_ = crate::leanh::lean_box(0);
                        v_isShared_2431_ = v_isSharedCheck_2435_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_2391_ = crate::leanh::lean_ctor_get(v_a_2387_, 0);
                crate::leanh::lean_inc_ref(v_toRing_2391_);
                crate::leanh::lean_dec(v_a_2387_);
                v_negFn_x3f_2392_ = crate::leanh::lean_ctor_get(v_toRing_2391_, 9);
                if crate::leanh::lean_obj_tag(v_negFn_x3f_2392_) == 1 {
                    crate::leanh::lean_inc_ref(v_negFn_x3f_2392_);
                    crate::leanh::lean_dec_ref(v_toRing_2391_);
                    v_val_2393_ = crate::leanh::lean_ctor_get(v_negFn_x3f_2392_, 0);
                    crate::leanh::lean_inc(v_val_2393_);
                    crate::leanh::lean_dec_ref_known(v_negFn_x3f_2392_, 1);
                    if v_isShared_2390_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2389_, 0, v_val_2393_);
                        v___x_2395_ = v___x_2389_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2396_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_val_2393_);
                        v___x_2395_ = v_reuseFailAlloc_2396_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2389_);
                    v_type_2397_ = crate::leanh::lean_ctor_get(v_toRing_2391_, 1);
                    crate::leanh::lean_inc_ref_n(v_type_2397_, 2);
                    v_u_2398_ = crate::leanh::lean_ctor_get(v_toRing_2391_, 2);
                    crate::leanh::lean_inc_n(v_u_2398_, 2);
                    v_ringInst_2399_ = crate::leanh::lean_ctor_get(v_toRing_2391_, 3);
                    crate::leanh::lean_inc_ref(v_ringInst_2399_);
                    crate::leanh::lean_dec_ref(v_toRing_2391_);
                    v___x_2400_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4;
                    v___x_2401_ = crate::leanh::lean_box(0);
                    v___x_2402_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2402_, 0, v_u_2398_);
                    crate::leanh::lean_ctor_set(v___x_2402_, 1, v___x_2401_);
                    v___x_2403_ = l_Lean_mkConst(v___x_2400_, v___x_2402_);
                    v_expectedInst_2404_ =
                        l_Lean_mkAppB(v___x_2403_, v_type_2397_, v_ringInst_2399_);
                    v___x_2405_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6;
                    v___x_2406_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8;
                    v___x_2407_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_2397_, v_u_2398_, v___x_2405_, v___x_2406_, v_expectedInst_2404_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
                    if crate::leanh::lean_obj_tag(v___x_2407_) == 0 {
                        v_a_2408_ = crate::leanh::lean_ctor_get(v___x_2407_, 0);
                        crate::leanh::lean_inc_n(v_a_2408_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_2407_, 1);
                        v___f_2409_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0 as *mut core::ffi::c_void, 2, 1);
                        crate::leanh::lean_closure_set(v___f_2409_, 0, v_a_2408_);
                        v___x_2410_ =
                            l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
                                v___f_2409_,
                                v___y_2374_,
                                v___y_2375_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_2410_) == 0 {
                            v_isSharedCheck_2417_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2410_)) as u8;
                            if v_isSharedCheck_2417_ == 0 {
                                v_unused_2418_ = crate::leanh::lean_ctor_get(v___x_2410_, 0);
                                crate::leanh::lean_dec(v_unused_2418_);
                                v___x_2412_ = v___x_2410_;
                                v_isShared_2413_ = v_isSharedCheck_2417_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2410_);
                                v___x_2412_ = crate::leanh::lean_box(0);
                                v_isShared_2413_ = v_isSharedCheck_2417_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2408_);
                            v_a_2419_ = crate::leanh::lean_ctor_get(v___x_2410_, 0);
                            v_isSharedCheck_2426_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2410_)) as u8;
                            if v_isSharedCheck_2426_ == 0 {
                                v___x_2421_ = v___x_2410_;
                                v_isShared_2422_ = v_isSharedCheck_2426_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2419_);
                                crate::leanh::lean_dec(v___x_2410_);
                                v___x_2421_ = crate::leanh::lean_box(0);
                                v_isShared_2422_ = v_isSharedCheck_2426_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        return v___x_2407_;
                    }
                }
            }
            2 => {
                return v___x_2395_;
            }
            3 => {
                if v_isShared_2413_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2412_, 0, v_a_2408_);
                    v___x_2415_ = v___x_2412_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2416_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2408_);
                    v___x_2415_ = v_reuseFailAlloc_2416_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2415_;
            }
            5 => {
                if v_isShared_2422_ == 0 {
                    v___x_2424_ = v___x_2421_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2425_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
                    v___x_2424_ = v_reuseFailAlloc_2425_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2424_;
            }
            7 => {
                if v_isShared_2431_ == 0 {
                    v___x_2433_ = v___x_2430_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2434_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
                    v___x_2433_ = v_reuseFailAlloc_2434_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___boxed(
    mut v___y_2436_: *mut crate::leanh::LeanObject,
    mut v___y_2437_: *mut crate::leanh::LeanObject,
    mut v___y_2438_: *mut crate::leanh::LeanObject,
    mut v___y_2439_: *mut crate::leanh::LeanObject,
    mut v___y_2440_: *mut crate::leanh::LeanObject,
    mut v___y_2441_: *mut crate::leanh::LeanObject,
    mut v___y_2442_: *mut crate::leanh::LeanObject,
    mut v___y_2443_: *mut crate::leanh::LeanObject,
    mut v___y_2444_: *mut crate::leanh::LeanObject,
    mut v___y_2445_: *mut crate::leanh::LeanObject,
    mut v___y_2446_: *mut crate::leanh::LeanObject,
    mut v___y_2447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2448_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
    crate::leanh::lean_dec(v___y_2446_);
    crate::leanh::lean_dec_ref(v___y_2445_);
    crate::leanh::lean_dec(v___y_2444_);
    crate::leanh::lean_dec_ref(v___y_2443_);
    crate::leanh::lean_dec(v___y_2442_);
    crate::leanh::lean_dec_ref(v___y_2441_);
    crate::leanh::lean_dec(v___y_2440_);
    crate::leanh::lean_dec_ref(v___y_2439_);
    crate::leanh::lean_dec(v___y_2438_);
    crate::leanh::lean_dec(v___y_2437_);
    crate::leanh::lean_dec_ref(v___y_2436_);
    return v_res_2448_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2456_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2457_ = lean_nat_to_int(v___x_2456_);
    return v___x_2457_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(
    mut v_k_2464_: *mut crate::leanh::LeanObject,
    mut v___y_2465_: *mut crate::leanh::LeanObject,
    mut v___y_2466_: *mut crate::leanh::LeanObject,
    mut v___y_2467_: *mut crate::leanh::LeanObject,
    mut v___y_2468_: *mut crate::leanh::LeanObject,
    mut v___y_2469_: *mut crate::leanh::LeanObject,
    mut v___y_2470_: *mut crate::leanh::LeanObject,
    mut v___y_2471_: *mut crate::leanh::LeanObject,
    mut v___y_2472_: *mut crate::leanh::LeanObject,
    mut v___y_2473_: *mut crate::leanh::LeanObject,
    mut v___y_2474_: *mut crate::leanh::LeanObject,
    mut v___y_2475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toRing_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2495_: u8 = 0;
    let mut v_ofNatInst_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: u8 = 0;
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2521_: u8 = 0;
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2526_: u8 = 0;
    let mut v_val_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2531_: u8 = 0;
    let mut v_a_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2535_: u8 = 0;
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2539_: u8 = 0;
    let mut v_a_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2543_: u8 = 0;
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2547_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2477_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v___y_2465_,
                    v___y_2466_,
                    v___y_2467_,
                    v___y_2468_,
                    v___y_2469_,
                    v___y_2470_,
                    v___y_2471_,
                    v___y_2472_,
                    v___y_2473_,
                    v___y_2474_,
                    v___y_2475_,
                );
                if crate::leanh::lean_obj_tag(v___x_2477_) == 0 {
                    v_a_2478_ = crate::leanh::lean_ctor_get(v___x_2477_, 0);
                    crate::leanh::lean_inc(v_a_2478_);
                    crate::leanh::lean_dec_ref_known(v___x_2477_, 1);
                    v_toRing_2479_ = crate::leanh::lean_ctor_get(v_a_2478_, 0);
                    crate::leanh::lean_inc_ref(v_toRing_2479_);
                    crate::leanh::lean_dec(v_a_2478_);
                    v_type_2480_ = crate::leanh::lean_ctor_get(v_toRing_2479_, 1);
                    crate::leanh::lean_inc_ref_n(v_type_2480_, 2);
                    v_u_2481_ = crate::leanh::lean_ctor_get(v_toRing_2479_, 2);
                    crate::leanh::lean_inc(v_u_2481_);
                    v_semiringInst_2482_ = crate::leanh::lean_ctor_get(v_toRing_2479_, 4);
                    crate::leanh::lean_inc_ref(v_semiringInst_2482_);
                    crate::leanh::lean_dec_ref(v_toRing_2479_);
                    v___x_2483_ = lean_nat_abs(v_k_2464_);
                    v_n_2484_ = l_Lean_mkRawNatLit(v___x_2483_);
                    v___x_2485_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1;
                    v___x_2486_ = crate::leanh::lean_box(0);
                    v___x_2487_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2487_, 0, v_u_2481_);
                    crate::leanh::lean_ctor_set(v___x_2487_, 1, v___x_2486_);
                    crate::leanh::lean_inc_ref(v___x_2487_);
                    v___x_2488_ = l_Lean_mkConst(v___x_2485_, v___x_2487_);
                    crate::leanh::lean_inc_ref(v_n_2484_);
                    v___x_2489_ = l_Lean_mkAppB(v___x_2488_, v_type_2480_, v_n_2484_);
                    v___x_2490_ = crate::leanh::lean_box(0);
                    v___x_2491_ = l_Lean_Meta_synthInstance_x3f(
                        v___x_2489_,
                        v___x_2490_,
                        v___y_2472_,
                        v___y_2473_,
                        v___y_2474_,
                        v___y_2475_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2491_) == 0 {
                        v_a_2492_ = crate::leanh::lean_ctor_get(v___x_2491_, 0);
                        v_isSharedCheck_2531_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2491_)) as u8;
                        if v_isSharedCheck_2531_ == 0 {
                            v___x_2494_ = v___x_2491_;
                            v_isShared_2495_ = v_isSharedCheck_2531_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2492_);
                            crate::leanh::lean_dec(v___x_2491_);
                            v___x_2494_ = crate::leanh::lean_box(0);
                            v_isShared_2495_ = v_isSharedCheck_2531_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_2487_, 2);
                        crate::leanh::lean_dec_ref(v_n_2484_);
                        crate::leanh::lean_dec_ref(v_semiringInst_2482_);
                        crate::leanh::lean_dec_ref(v_type_2480_);
                        v_a_2532_ = crate::leanh::lean_ctor_get(v___x_2491_, 0);
                        v_isSharedCheck_2539_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2491_)) as u8;
                        if v_isSharedCheck_2539_ == 0 {
                            v___x_2534_ = v___x_2491_;
                            v_isShared_2535_ = v_isSharedCheck_2539_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2532_);
                            crate::leanh::lean_dec(v___x_2491_);
                            v___x_2534_ = crate::leanh::lean_box(0);
                            v_isShared_2535_ = v_isSharedCheck_2539_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v_a_2540_ = crate::leanh::lean_ctor_get(v___x_2477_, 0);
                    v_isSharedCheck_2547_ = (!crate::leanh::lean_is_exclusive(v___x_2477_)) as u8;
                    if v_isSharedCheck_2547_ == 0 {
                        v___x_2542_ = v___x_2477_;
                        v_isShared_2543_ = v_isSharedCheck_2547_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2540_);
                        crate::leanh::lean_dec(v___x_2477_);
                        v___x_2542_ = crate::leanh::lean_box(0);
                        v_isShared_2543_ = v_isSharedCheck_2547_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2492_) == 1 {
                    crate::leanh::lean_dec_ref(v_semiringInst_2482_);
                    v_val_2527_ = crate::leanh::lean_ctor_get(v_a_2492_, 0);
                    crate::leanh::lean_inc(v_val_2527_);
                    crate::leanh::lean_dec_ref_known(v_a_2492_, 1);
                    v_ofNatInst_2497_ = v_val_2527_;
                    v___y_2498_ = v___y_2465_;
                    v___y_2499_ = v___y_2466_;
                    v___y_2500_ = v___y_2467_;
                    v___y_2501_ = v___y_2468_;
                    v___y_2502_ = v___y_2469_;
                    v___y_2503_ = v___y_2470_;
                    v___y_2504_ = v___y_2471_;
                    v___y_2505_ = v___y_2472_;
                    v___y_2506_ = v___y_2473_;
                    v___y_2507_ = v___y_2474_;
                    v___y_2508_ = v___y_2475_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_2492_);
                    v___x_2528_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6;
                    crate::leanh::lean_inc_ref(v___x_2487_);
                    v___x_2529_ = l_Lean_mkConst(v___x_2528_, v___x_2487_);
                    crate::leanh::lean_inc_ref(v_n_2484_);
                    crate::leanh::lean_inc_ref(v_type_2480_);
                    v___x_2530_ =
                        l_Lean_mkApp3(v___x_2529_, v_type_2480_, v_semiringInst_2482_, v_n_2484_);
                    v_ofNatInst_2497_ = v___x_2530_;
                    v___y_2498_ = v___y_2465_;
                    v___y_2499_ = v___y_2466_;
                    v___y_2500_ = v___y_2467_;
                    v___y_2501_ = v___y_2468_;
                    v___y_2502_ = v___y_2469_;
                    v___y_2503_ = v___y_2470_;
                    v___y_2504_ = v___y_2471_;
                    v___y_2505_ = v___y_2472_;
                    v___y_2506_ = v___y_2473_;
                    v___y_2507_ = v___y_2474_;
                    v___y_2508_ = v___y_2475_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2509_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3;
                v___x_2510_ = l_Lean_mkConst(v___x_2509_, v___x_2487_);
                v_n_2511_ = l_Lean_mkApp3(v___x_2510_, v_type_2480_, v_n_2484_, v_ofNatInst_2497_);
                v___x_2512_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once), _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
                v___x_2513_ = lean_int_dec_lt(v_k_2464_, v___x_2512_);
                if v___x_2513_ == 0 {
                    if v_isShared_2495_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2494_, 0, v_n_2511_);
                        v___x_2515_ = v___x_2494_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2516_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_n_2511_);
                        v___x_2515_ = v_reuseFailAlloc_2516_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2494_);
                    v___x_2517_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
                    if crate::leanh::lean_obj_tag(v___x_2517_) == 0 {
                        v_a_2518_ = crate::leanh::lean_ctor_get(v___x_2517_, 0);
                        v_isSharedCheck_2526_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2517_)) as u8;
                        if v_isSharedCheck_2526_ == 0 {
                            v___x_2520_ = v___x_2517_;
                            v_isShared_2521_ = v_isSharedCheck_2526_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2518_);
                            crate::leanh::lean_dec(v___x_2517_);
                            v___x_2520_ = crate::leanh::lean_box(0);
                            v_isShared_2521_ = v_isSharedCheck_2526_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_n_2511_);
                        return v___x_2517_;
                    }
                }
            }
            3 => {
                return v___x_2515_;
            }
            4 => {
                v___x_2522_ = l_Lean_Expr_app___override(v_a_2518_, v_n_2511_);
                if v_isShared_2521_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2520_, 0, v___x_2522_);
                    v___x_2524_ = v___x_2520_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2525_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
                    v___x_2524_ = v_reuseFailAlloc_2525_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2524_;
            }
            6 => {
                if v_isShared_2535_ == 0 {
                    v___x_2537_ = v___x_2534_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2538_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
                    v___x_2537_ = v_reuseFailAlloc_2538_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2537_;
            }
            8 => {
                if v_isShared_2543_ == 0 {
                    v___x_2545_ = v___x_2542_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2546_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
                    v___x_2545_ = v_reuseFailAlloc_2546_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2545_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___boxed(
    mut v_k_2548_: *mut crate::leanh::LeanObject,
    mut v___y_2549_: *mut crate::leanh::LeanObject,
    mut v___y_2550_: *mut crate::leanh::LeanObject,
    mut v___y_2551_: *mut crate::leanh::LeanObject,
    mut v___y_2552_: *mut crate::leanh::LeanObject,
    mut v___y_2553_: *mut crate::leanh::LeanObject,
    mut v___y_2554_: *mut crate::leanh::LeanObject,
    mut v___y_2555_: *mut crate::leanh::LeanObject,
    mut v___y_2556_: *mut crate::leanh::LeanObject,
    mut v___y_2557_: *mut crate::leanh::LeanObject,
    mut v___y_2558_: *mut crate::leanh::LeanObject,
    mut v___y_2559_: *mut crate::leanh::LeanObject,
    mut v___y_2560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2561_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
    crate::leanh::lean_dec(v___y_2559_);
    crate::leanh::lean_dec_ref(v___y_2558_);
    crate::leanh::lean_dec(v___y_2557_);
    crate::leanh::lean_dec_ref(v___y_2556_);
    crate::leanh::lean_dec(v___y_2555_);
    crate::leanh::lean_dec_ref(v___y_2554_);
    crate::leanh::lean_dec(v___y_2553_);
    crate::leanh::lean_dec_ref(v___y_2552_);
    crate::leanh::lean_dec(v___y_2551_);
    crate::leanh::lean_dec(v___y_2550_);
    crate::leanh::lean_dec_ref(v___y_2549_);
    crate::leanh::lean_dec(v_k_2548_);
    return v_res_2561_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0(
    mut v_a_2562_: *mut crate::leanh::LeanObject,
    mut v_s_2563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_2578_: u8 = 0;
    let mut v_invSet_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_2582_: u8 = 0;
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2585_: u8 = 0;
    let mut v_id_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2604_: u8 = 0;
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2612_: u8 = 0;
    let mut v_unused_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2564_ = crate::leanh::lean_ctor_get(v_s_2563_, 0);
                v_invFn_x3f_2565_ = crate::leanh::lean_ctor_get(v_s_2563_, 1);
                v_semiringId_x3f_2566_ = crate::leanh::lean_ctor_get(v_s_2563_, 2);
                v_commSemiringInst_2567_ = crate::leanh::lean_ctor_get(v_s_2563_, 3);
                v_commRingInst_2568_ = crate::leanh::lean_ctor_get(v_s_2563_, 4);
                v_noZeroDivInst_x3f_2569_ = crate::leanh::lean_ctor_get(v_s_2563_, 5);
                v_fieldInst_x3f_2570_ = crate::leanh::lean_ctor_get(v_s_2563_, 6);
                v_powIdentityInst_x3f_2571_ = crate::leanh::lean_ctor_get(v_s_2563_, 7);
                v_denoteEntries_2572_ = crate::leanh::lean_ctor_get(v_s_2563_, 8);
                v_nextId_2573_ = crate::leanh::lean_ctor_get(v_s_2563_, 9);
                v_steps_2574_ = crate::leanh::lean_ctor_get(v_s_2563_, 10);
                v_queue_2575_ = crate::leanh::lean_ctor_get(v_s_2563_, 11);
                v_basis_2576_ = crate::leanh::lean_ctor_get(v_s_2563_, 12);
                v_diseqs_2577_ = crate::leanh::lean_ctor_get(v_s_2563_, 13);
                v_recheck_2578_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2563_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_2579_ = crate::leanh::lean_ctor_get(v_s_2563_, 14);
                v_powIdentityVarCount_2580_ = crate::leanh::lean_ctor_get(v_s_2563_, 15);
                v_numEq0_x3f_2581_ = crate::leanh::lean_ctor_get(v_s_2563_, 16);
                v_numEq0Updated_2582_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2563_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_2614_ = (!crate::leanh::lean_is_exclusive(v_s_2563_)) as u8;
                if v_isSharedCheck_2614_ == 0 {
                    v___x_2584_ = v_s_2563_;
                    v_isShared_2585_ = v_isSharedCheck_2614_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numEq0_x3f_2581_);
                    crate::leanh::lean_inc(v_powIdentityVarCount_2580_);
                    crate::leanh::lean_inc(v_invSet_2579_);
                    crate::leanh::lean_inc(v_diseqs_2577_);
                    crate::leanh::lean_inc(v_basis_2576_);
                    crate::leanh::lean_inc(v_queue_2575_);
                    crate::leanh::lean_inc(v_steps_2574_);
                    crate::leanh::lean_inc(v_nextId_2573_);
                    crate::leanh::lean_inc(v_denoteEntries_2572_);
                    crate::leanh::lean_inc(v_powIdentityInst_x3f_2571_);
                    crate::leanh::lean_inc(v_fieldInst_x3f_2570_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_2569_);
                    crate::leanh::lean_inc(v_commRingInst_2568_);
                    crate::leanh::lean_inc(v_commSemiringInst_2567_);
                    crate::leanh::lean_inc(v_semiringId_x3f_2566_);
                    crate::leanh::lean_inc(v_invFn_x3f_2565_);
                    crate::leanh::lean_inc(v_toRing_2564_);
                    crate::leanh::lean_dec(v_s_2563_);
                    v___x_2584_ = crate::leanh::lean_box(0);
                    v_isShared_2585_ = v_isSharedCheck_2614_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_2586_ = crate::leanh::lean_ctor_get(v_toRing_2564_, 0);
                v_type_2587_ = crate::leanh::lean_ctor_get(v_toRing_2564_, 1);
                v_u_2588_ = crate::leanh::lean_ctor_get(v_toRing_2564_, 2);
                v_ringInst_2589_ = crate::leanh::lean_ctor_get(v_toRing_2564_, 3);
                v_semiringInst_2590_ = crate::leanh::lean_ctor_get(v_toRing_2564_, 4);
                v_charInst_x3f_2591_ = crate::leanh::lean_ctor_get(v_toRing_2564_, 5);
                v_mulFn_x3f_2592_ = crate::leanh::lean_ctor_get(v_toRing_2564_, 7);
                v_subFn_x3f_2593_ = crate::leanh::lean_ctor_get(v_toRing_2564_, 8);
                v_negFn_x3f_2594_ = crate::leanh::lean_ctor_get(v_toRing_2564_, 9);
                v_powFn_x3f_2595_ = crate::leanh::lean_ctor_get(v_toRing_2564_, 10);
                v_intCastFn_x3f_2596_ = crate::leanh::lean_ctor_get(v_toRing_2564_, 11);
                v_natCastFn_x3f_2597_ = crate::leanh::lean_ctor_get(v_toRing_2564_, 12);
                v_one_x3f_2598_ = crate::leanh::lean_ctor_get(v_toRing_2564_, 13);
                v_vars_2599_ = crate::leanh::lean_ctor_get(v_toRing_2564_, 14);
                v_varMap_2600_ = crate::leanh::lean_ctor_get(v_toRing_2564_, 15);
                v_denote_2601_ = crate::leanh::lean_ctor_get(v_toRing_2564_, 16);
                v_isSharedCheck_2612_ = (!crate::leanh::lean_is_exclusive(v_toRing_2564_)) as u8;
                if v_isSharedCheck_2612_ == 0 {
                    v_unused_2613_ = crate::leanh::lean_ctor_get(v_toRing_2564_, 6);
                    crate::leanh::lean_dec(v_unused_2613_);
                    v___x_2603_ = v_toRing_2564_;
                    v_isShared_2604_ = v_isSharedCheck_2612_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_2601_);
                    crate::leanh::lean_inc(v_varMap_2600_);
                    crate::leanh::lean_inc(v_vars_2599_);
                    crate::leanh::lean_inc(v_one_x3f_2598_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_2597_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_2596_);
                    crate::leanh::lean_inc(v_powFn_x3f_2595_);
                    crate::leanh::lean_inc(v_negFn_x3f_2594_);
                    crate::leanh::lean_inc(v_subFn_x3f_2593_);
                    crate::leanh::lean_inc(v_mulFn_x3f_2592_);
                    crate::leanh::lean_inc(v_charInst_x3f_2591_);
                    crate::leanh::lean_inc(v_semiringInst_2590_);
                    crate::leanh::lean_inc(v_ringInst_2589_);
                    crate::leanh::lean_inc(v_u_2588_);
                    crate::leanh::lean_inc(v_type_2587_);
                    crate::leanh::lean_inc(v_id_2586_);
                    crate::leanh::lean_dec(v_toRing_2564_);
                    v___x_2603_ = crate::leanh::lean_box(0);
                    v_isShared_2604_ = v_isSharedCheck_2612_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2605_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2605_, 0, v_a_2562_);
                if v_isShared_2604_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2603_, 6, v___x_2605_);
                    v___x_2607_ = v___x_2603_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2611_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_id_2586_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_type_2587_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 2, v_u_2588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 3, v_ringInst_2589_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 4, v_semiringInst_2590_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 5, v_charInst_x3f_2591_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 6, v___x_2605_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 7, v_mulFn_x3f_2592_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 8, v_subFn_x3f_2593_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 9, v_negFn_x3f_2594_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 10, v_powFn_x3f_2595_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 11, v_intCastFn_x3f_2596_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 12, v_natCastFn_x3f_2597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 13, v_one_x3f_2598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 14, v_vars_2599_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 15, v_varMap_2600_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 16, v_denote_2601_);
                    v___x_2607_ = v_reuseFailAlloc_2611_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2585_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2584_, 0, v___x_2607_);
                    v___x_2609_ = v___x_2584_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2610_ = crate::leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2607_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_invFn_x3f_2565_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 2, v_semiringId_x3f_2566_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2610_,
                        3,
                        v_commSemiringInst_2567_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 4, v_commRingInst_2568_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2610_,
                        5,
                        v_noZeroDivInst_x3f_2569_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 6, v_fieldInst_x3f_2570_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2610_,
                        7,
                        v_powIdentityInst_x3f_2571_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 8, v_denoteEntries_2572_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 9, v_nextId_2573_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 10, v_steps_2574_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 11, v_queue_2575_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 12, v_basis_2576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 13, v_diseqs_2577_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 14, v_invSet_2579_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2610_,
                        15,
                        v_powIdentityVarCount_2580_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 16, v_numEq0_x3f_2581_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2610_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_recheck_2578_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2610_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_2582_,
                    );
                    v___x_2609_ = v_reuseFailAlloc_2610_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2609_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(
    mut v_type_2615_: *mut crate::leanh::LeanObject,
    mut v_u_2616_: *mut crate::leanh::LeanObject,
    mut v_instDeclName_2617_: *mut crate::leanh::LeanObject,
    mut v_declName_2618_: *mut crate::leanh::LeanObject,
    mut v_expectedInst_2619_: *mut crate::leanh::LeanObject,
    mut v___y_2620_: *mut crate::leanh::LeanObject,
    mut v___y_2621_: *mut crate::leanh::LeanObject,
    mut v___y_2622_: *mut crate::leanh::LeanObject,
    mut v___y_2623_: *mut crate::leanh::LeanObject,
    mut v___y_2624_: *mut crate::leanh::LeanObject,
    mut v___y_2625_: *mut crate::leanh::LeanObject,
    mut v___y_2626_: *mut crate::leanh::LeanObject,
    mut v___y_2627_: *mut crate::leanh::LeanObject,
    mut v___y_2628_: *mut crate::leanh::LeanObject,
    mut v___y_2629_: *mut crate::leanh::LeanObject,
    mut v___y_2630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2649_: u8 = 0;
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2632_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_n(v_u_2616_, 2);
                v___x_2633_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2633_, 0, v_u_2616_);
                crate::leanh::lean_ctor_set(v___x_2633_, 1, v___x_2632_);
                v___x_2634_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2634_, 0, v_u_2616_);
                crate::leanh::lean_ctor_set(v___x_2634_, 1, v___x_2633_);
                v___x_2635_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2635_, 0, v_u_2616_);
                crate::leanh::lean_ctor_set(v___x_2635_, 1, v___x_2634_);
                crate::leanh::lean_inc_ref(v___x_2635_);
                v___x_2636_ = l_Lean_mkConst(v_instDeclName_2617_, v___x_2635_);
                crate::leanh::lean_inc_ref_n(v_type_2615_, 3);
                v___x_2637_ = l_Lean_mkApp3(v___x_2636_, v_type_2615_, v_type_2615_, v_type_2615_);
                v___x_2638_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_2637_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
                if crate::leanh::lean_obj_tag(v___x_2638_) == 0 {
                    v_a_2639_ = crate::leanh::lean_ctor_get(v___x_2638_, 0);
                    crate::leanh::lean_inc_n(v_a_2639_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2638_, 1);
                    crate::leanh::lean_inc(v_declName_2618_);
                    v___x_2640_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
                        v_declName_2618_,
                        v_a_2639_,
                        v_expectedInst_2619_,
                        v___y_2627_,
                        v___y_2628_,
                        v___y_2629_,
                        v___y_2630_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2640_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2640_, 1);
                        v___x_2641_ = l_Lean_mkConst(v_declName_2618_, v___x_2635_);
                        crate::leanh::lean_inc_ref_n(v_type_2615_, 2);
                        v___x_2642_ = l_Lean_mkApp4(
                            v___x_2641_,
                            v_type_2615_,
                            v_type_2615_,
                            v_type_2615_,
                            v_a_2639_,
                        );
                        v___x_2643_ = l_Lean_Meta_Sym_canon(
                            v___x_2642_,
                            v___y_2625_,
                            v___y_2626_,
                            v___y_2627_,
                            v___y_2628_,
                            v___y_2629_,
                            v___y_2630_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2643_) == 0 {
                            v_a_2644_ = crate::leanh::lean_ctor_get(v___x_2643_, 0);
                            crate::leanh::lean_inc(v_a_2644_);
                            crate::leanh::lean_dec_ref_known(v___x_2643_, 1);
                            v___x_2645_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_2644_, v___y_2626_);
                            return v___x_2645_;
                        } else {
                            return v___x_2643_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2639_);
                        crate::leanh::lean_dec_ref_known(v___x_2635_, 2);
                        crate::leanh::lean_dec(v_declName_2618_);
                        crate::leanh::lean_dec_ref(v_type_2615_);
                        v_a_2646_ = crate::leanh::lean_ctor_get(v___x_2640_, 0);
                        v_isSharedCheck_2653_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2640_)) as u8;
                        if v_isSharedCheck_2653_ == 0 {
                            v___x_2648_ = v___x_2640_;
                            v_isShared_2649_ = v_isSharedCheck_2653_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2646_);
                            crate::leanh::lean_dec(v___x_2640_);
                            v___x_2648_ = crate::leanh::lean_box(0);
                            v_isShared_2649_ = v_isSharedCheck_2653_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2635_, 2);
                    crate::leanh::lean_dec_ref(v_expectedInst_2619_);
                    crate::leanh::lean_dec(v_declName_2618_);
                    crate::leanh::lean_dec_ref(v_type_2615_);
                    return v___x_2638_;
                }
            }
            1 => {
                if v_isShared_2649_ == 0 {
                    v___x_2651_ = v___x_2648_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2652_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
                    v___x_2651_ = v_reuseFailAlloc_2652_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2651_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_2654_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_u_2655_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_instDeclName_2656_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_declName_2657_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_expectedInst_2658_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_2659_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_2660_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_2661_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_2662_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_2663_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_2664_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_2665_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2666_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2667_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2668_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2669_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2670_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2671_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_2654_, v_u_2655_, v_instDeclName_2656_, v_declName_2657_, v_expectedInst_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
    crate::leanh::lean_dec(v___y_2669_);
    crate::leanh::lean_dec_ref(v___y_2668_);
    crate::leanh::lean_dec(v___y_2667_);
    crate::leanh::lean_dec_ref(v___y_2666_);
    crate::leanh::lean_dec(v___y_2665_);
    crate::leanh::lean_dec_ref(v___y_2664_);
    crate::leanh::lean_dec(v___y_2663_);
    crate::leanh::lean_dec_ref(v___y_2662_);
    crate::leanh::lean_dec(v___y_2661_);
    crate::leanh::lean_dec(v___y_2660_);
    crate::leanh::lean_dec_ref(v___y_2659_);
    return v_res_2671_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(
    mut v___y_2688_: *mut crate::leanh::LeanObject,
    mut v___y_2689_: *mut crate::leanh::LeanObject,
    mut v___y_2690_: *mut crate::leanh::LeanObject,
    mut v___y_2691_: *mut crate::leanh::LeanObject,
    mut v___y_2692_: *mut crate::leanh::LeanObject,
    mut v___y_2693_: *mut crate::leanh::LeanObject,
    mut v___y_2694_: *mut crate::leanh::LeanObject,
    mut v___y_2695_: *mut crate::leanh::LeanObject,
    mut v___y_2696_: *mut crate::leanh::LeanObject,
    mut v___y_2697_: *mut crate::leanh::LeanObject,
    mut v___y_2698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2704_: u8 = 0;
    let mut v_toRing_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedInst_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2730_: u8 = 0;
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2734_: u8 = 0;
    let mut v_unused_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2739_: u8 = 0;
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2743_: u8 = 0;
    let mut v_isSharedCheck_2744_: u8 = 0;
    let mut v_a_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2748_: u8 = 0;
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2700_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v___y_2688_,
                    v___y_2689_,
                    v___y_2690_,
                    v___y_2691_,
                    v___y_2692_,
                    v___y_2693_,
                    v___y_2694_,
                    v___y_2695_,
                    v___y_2696_,
                    v___y_2697_,
                    v___y_2698_,
                );
                if crate::leanh::lean_obj_tag(v___x_2700_) == 0 {
                    v_a_2701_ = crate::leanh::lean_ctor_get(v___x_2700_, 0);
                    v_isSharedCheck_2744_ = (!crate::leanh::lean_is_exclusive(v___x_2700_)) as u8;
                    if v_isSharedCheck_2744_ == 0 {
                        v___x_2703_ = v___x_2700_;
                        v_isShared_2704_ = v_isSharedCheck_2744_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2701_);
                        crate::leanh::lean_dec(v___x_2700_);
                        v___x_2703_ = crate::leanh::lean_box(0);
                        v_isShared_2704_ = v_isSharedCheck_2744_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2745_ = crate::leanh::lean_ctor_get(v___x_2700_, 0);
                    v_isSharedCheck_2752_ = (!crate::leanh::lean_is_exclusive(v___x_2700_)) as u8;
                    if v_isSharedCheck_2752_ == 0 {
                        v___x_2747_ = v___x_2700_;
                        v_isShared_2748_ = v_isSharedCheck_2752_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2745_);
                        crate::leanh::lean_dec(v___x_2700_);
                        v___x_2747_ = crate::leanh::lean_box(0);
                        v_isShared_2748_ = v_isSharedCheck_2752_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_2705_ = crate::leanh::lean_ctor_get(v_a_2701_, 0);
                crate::leanh::lean_inc_ref(v_toRing_2705_);
                crate::leanh::lean_dec(v_a_2701_);
                v_addFn_x3f_2706_ = crate::leanh::lean_ctor_get(v_toRing_2705_, 6);
                if crate::leanh::lean_obj_tag(v_addFn_x3f_2706_) == 1 {
                    crate::leanh::lean_inc_ref(v_addFn_x3f_2706_);
                    crate::leanh::lean_dec_ref(v_toRing_2705_);
                    v_val_2707_ = crate::leanh::lean_ctor_get(v_addFn_x3f_2706_, 0);
                    crate::leanh::lean_inc(v_val_2707_);
                    crate::leanh::lean_dec_ref_known(v_addFn_x3f_2706_, 1);
                    if v_isShared_2704_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2703_, 0, v_val_2707_);
                        v___x_2709_ = v___x_2703_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2710_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_val_2707_);
                        v___x_2709_ = v_reuseFailAlloc_2710_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2703_);
                    v_type_2711_ = crate::leanh::lean_ctor_get(v_toRing_2705_, 1);
                    crate::leanh::lean_inc_ref_n(v_type_2711_, 3);
                    v_u_2712_ = crate::leanh::lean_ctor_get(v_toRing_2705_, 2);
                    crate::leanh::lean_inc_n(v_u_2712_, 2);
                    v_semiringInst_2713_ = crate::leanh::lean_ctor_get(v_toRing_2705_, 4);
                    crate::leanh::lean_inc_ref(v_semiringInst_2713_);
                    crate::leanh::lean_dec_ref(v_toRing_2705_);
                    v___x_2714_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1;
                    v___x_2715_ = crate::leanh::lean_box(0);
                    v___x_2716_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2716_, 0, v_u_2712_);
                    crate::leanh::lean_ctor_set(v___x_2716_, 1, v___x_2715_);
                    crate::leanh::lean_inc_ref(v___x_2716_);
                    v___x_2717_ = l_Lean_mkConst(v___x_2714_, v___x_2716_);
                    v___x_2718_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3;
                    v___x_2719_ = l_Lean_mkConst(v___x_2718_, v___x_2716_);
                    v___x_2720_ = l_Lean_mkAppB(v___x_2719_, v_type_2711_, v_semiringInst_2713_);
                    v_expectedInst_2721_ = l_Lean_mkAppB(v___x_2717_, v_type_2711_, v___x_2720_);
                    v___x_2722_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5;
                    v___x_2723_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7;
                    v___x_2724_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_2711_, v_u_2712_, v___x_2722_, v___x_2723_, v_expectedInst_2721_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
                    if crate::leanh::lean_obj_tag(v___x_2724_) == 0 {
                        v_a_2725_ = crate::leanh::lean_ctor_get(v___x_2724_, 0);
                        crate::leanh::lean_inc_n(v_a_2725_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_2724_, 1);
                        v___f_2726_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0 as *mut core::ffi::c_void, 2, 1);
                        crate::leanh::lean_closure_set(v___f_2726_, 0, v_a_2725_);
                        v___x_2727_ =
                            l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
                                v___f_2726_,
                                v___y_2688_,
                                v___y_2689_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_2727_) == 0 {
                            v_isSharedCheck_2734_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2727_)) as u8;
                            if v_isSharedCheck_2734_ == 0 {
                                v_unused_2735_ = crate::leanh::lean_ctor_get(v___x_2727_, 0);
                                crate::leanh::lean_dec(v_unused_2735_);
                                v___x_2729_ = v___x_2727_;
                                v_isShared_2730_ = v_isSharedCheck_2734_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2727_);
                                v___x_2729_ = crate::leanh::lean_box(0);
                                v_isShared_2730_ = v_isSharedCheck_2734_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2725_);
                            v_a_2736_ = crate::leanh::lean_ctor_get(v___x_2727_, 0);
                            v_isSharedCheck_2743_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2727_)) as u8;
                            if v_isSharedCheck_2743_ == 0 {
                                v___x_2738_ = v___x_2727_;
                                v_isShared_2739_ = v_isSharedCheck_2743_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2736_);
                                crate::leanh::lean_dec(v___x_2727_);
                                v___x_2738_ = crate::leanh::lean_box(0);
                                v_isShared_2739_ = v_isSharedCheck_2743_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        return v___x_2724_;
                    }
                }
            }
            2 => {
                return v___x_2709_;
            }
            3 => {
                if v_isShared_2730_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2729_, 0, v_a_2725_);
                    v___x_2732_ = v___x_2729_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2733_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2725_);
                    v___x_2732_ = v_reuseFailAlloc_2733_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2732_;
            }
            5 => {
                if v_isShared_2739_ == 0 {
                    v___x_2741_ = v___x_2738_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2742_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
                    v___x_2741_ = v_reuseFailAlloc_2742_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2741_;
            }
            7 => {
                if v_isShared_2748_ == 0 {
                    v___x_2750_ = v___x_2747_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2751_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
                    v___x_2750_ = v_reuseFailAlloc_2751_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2750_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___boxed(
    mut v___y_2753_: *mut crate::leanh::LeanObject,
    mut v___y_2754_: *mut crate::leanh::LeanObject,
    mut v___y_2755_: *mut crate::leanh::LeanObject,
    mut v___y_2756_: *mut crate::leanh::LeanObject,
    mut v___y_2757_: *mut crate::leanh::LeanObject,
    mut v___y_2758_: *mut crate::leanh::LeanObject,
    mut v___y_2759_: *mut crate::leanh::LeanObject,
    mut v___y_2760_: *mut crate::leanh::LeanObject,
    mut v___y_2761_: *mut crate::leanh::LeanObject,
    mut v___y_2762_: *mut crate::leanh::LeanObject,
    mut v___y_2763_: *mut crate::leanh::LeanObject,
    mut v___y_2764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2765_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
    crate::leanh::lean_dec(v___y_2763_);
    crate::leanh::lean_dec_ref(v___y_2762_);
    crate::leanh::lean_dec(v___y_2761_);
    crate::leanh::lean_dec_ref(v___y_2760_);
    crate::leanh::lean_dec(v___y_2759_);
    crate::leanh::lean_dec_ref(v___y_2758_);
    crate::leanh::lean_dec(v___y_2757_);
    crate::leanh::lean_dec_ref(v___y_2756_);
    crate::leanh::lean_dec(v___y_2755_);
    crate::leanh::lean_dec(v___y_2754_);
    crate::leanh::lean_dec_ref(v___y_2753_);
    return v_res_2765_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0(
    mut v_a_2766_: *mut crate::leanh::LeanObject,
    mut v_s_2767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_2782_: u8 = 0;
    let mut v_invSet_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_2786_: u8 = 0;
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2789_: u8 = 0;
    let mut v_id_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2808_: u8 = 0;
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2816_: u8 = 0;
    let mut v_unused_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2818_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2768_ = crate::leanh::lean_ctor_get(v_s_2767_, 0);
                v_invFn_x3f_2769_ = crate::leanh::lean_ctor_get(v_s_2767_, 1);
                v_semiringId_x3f_2770_ = crate::leanh::lean_ctor_get(v_s_2767_, 2);
                v_commSemiringInst_2771_ = crate::leanh::lean_ctor_get(v_s_2767_, 3);
                v_commRingInst_2772_ = crate::leanh::lean_ctor_get(v_s_2767_, 4);
                v_noZeroDivInst_x3f_2773_ = crate::leanh::lean_ctor_get(v_s_2767_, 5);
                v_fieldInst_x3f_2774_ = crate::leanh::lean_ctor_get(v_s_2767_, 6);
                v_powIdentityInst_x3f_2775_ = crate::leanh::lean_ctor_get(v_s_2767_, 7);
                v_denoteEntries_2776_ = crate::leanh::lean_ctor_get(v_s_2767_, 8);
                v_nextId_2777_ = crate::leanh::lean_ctor_get(v_s_2767_, 9);
                v_steps_2778_ = crate::leanh::lean_ctor_get(v_s_2767_, 10);
                v_queue_2779_ = crate::leanh::lean_ctor_get(v_s_2767_, 11);
                v_basis_2780_ = crate::leanh::lean_ctor_get(v_s_2767_, 12);
                v_diseqs_2781_ = crate::leanh::lean_ctor_get(v_s_2767_, 13);
                v_recheck_2782_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2767_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_2783_ = crate::leanh::lean_ctor_get(v_s_2767_, 14);
                v_powIdentityVarCount_2784_ = crate::leanh::lean_ctor_get(v_s_2767_, 15);
                v_numEq0_x3f_2785_ = crate::leanh::lean_ctor_get(v_s_2767_, 16);
                v_numEq0Updated_2786_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2767_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_2818_ = (!crate::leanh::lean_is_exclusive(v_s_2767_)) as u8;
                if v_isSharedCheck_2818_ == 0 {
                    v___x_2788_ = v_s_2767_;
                    v_isShared_2789_ = v_isSharedCheck_2818_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numEq0_x3f_2785_);
                    crate::leanh::lean_inc(v_powIdentityVarCount_2784_);
                    crate::leanh::lean_inc(v_invSet_2783_);
                    crate::leanh::lean_inc(v_diseqs_2781_);
                    crate::leanh::lean_inc(v_basis_2780_);
                    crate::leanh::lean_inc(v_queue_2779_);
                    crate::leanh::lean_inc(v_steps_2778_);
                    crate::leanh::lean_inc(v_nextId_2777_);
                    crate::leanh::lean_inc(v_denoteEntries_2776_);
                    crate::leanh::lean_inc(v_powIdentityInst_x3f_2775_);
                    crate::leanh::lean_inc(v_fieldInst_x3f_2774_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_2773_);
                    crate::leanh::lean_inc(v_commRingInst_2772_);
                    crate::leanh::lean_inc(v_commSemiringInst_2771_);
                    crate::leanh::lean_inc(v_semiringId_x3f_2770_);
                    crate::leanh::lean_inc(v_invFn_x3f_2769_);
                    crate::leanh::lean_inc(v_toRing_2768_);
                    crate::leanh::lean_dec(v_s_2767_);
                    v___x_2788_ = crate::leanh::lean_box(0);
                    v_isShared_2789_ = v_isSharedCheck_2818_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_2790_ = crate::leanh::lean_ctor_get(v_toRing_2768_, 0);
                v_type_2791_ = crate::leanh::lean_ctor_get(v_toRing_2768_, 1);
                v_u_2792_ = crate::leanh::lean_ctor_get(v_toRing_2768_, 2);
                v_ringInst_2793_ = crate::leanh::lean_ctor_get(v_toRing_2768_, 3);
                v_semiringInst_2794_ = crate::leanh::lean_ctor_get(v_toRing_2768_, 4);
                v_charInst_x3f_2795_ = crate::leanh::lean_ctor_get(v_toRing_2768_, 5);
                v_addFn_x3f_2796_ = crate::leanh::lean_ctor_get(v_toRing_2768_, 6);
                v_subFn_x3f_2797_ = crate::leanh::lean_ctor_get(v_toRing_2768_, 8);
                v_negFn_x3f_2798_ = crate::leanh::lean_ctor_get(v_toRing_2768_, 9);
                v_powFn_x3f_2799_ = crate::leanh::lean_ctor_get(v_toRing_2768_, 10);
                v_intCastFn_x3f_2800_ = crate::leanh::lean_ctor_get(v_toRing_2768_, 11);
                v_natCastFn_x3f_2801_ = crate::leanh::lean_ctor_get(v_toRing_2768_, 12);
                v_one_x3f_2802_ = crate::leanh::lean_ctor_get(v_toRing_2768_, 13);
                v_vars_2803_ = crate::leanh::lean_ctor_get(v_toRing_2768_, 14);
                v_varMap_2804_ = crate::leanh::lean_ctor_get(v_toRing_2768_, 15);
                v_denote_2805_ = crate::leanh::lean_ctor_get(v_toRing_2768_, 16);
                v_isSharedCheck_2816_ = (!crate::leanh::lean_is_exclusive(v_toRing_2768_)) as u8;
                if v_isSharedCheck_2816_ == 0 {
                    v_unused_2817_ = crate::leanh::lean_ctor_get(v_toRing_2768_, 7);
                    crate::leanh::lean_dec(v_unused_2817_);
                    v___x_2807_ = v_toRing_2768_;
                    v_isShared_2808_ = v_isSharedCheck_2816_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_2805_);
                    crate::leanh::lean_inc(v_varMap_2804_);
                    crate::leanh::lean_inc(v_vars_2803_);
                    crate::leanh::lean_inc(v_one_x3f_2802_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_2801_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_2800_);
                    crate::leanh::lean_inc(v_powFn_x3f_2799_);
                    crate::leanh::lean_inc(v_negFn_x3f_2798_);
                    crate::leanh::lean_inc(v_subFn_x3f_2797_);
                    crate::leanh::lean_inc(v_addFn_x3f_2796_);
                    crate::leanh::lean_inc(v_charInst_x3f_2795_);
                    crate::leanh::lean_inc(v_semiringInst_2794_);
                    crate::leanh::lean_inc(v_ringInst_2793_);
                    crate::leanh::lean_inc(v_u_2792_);
                    crate::leanh::lean_inc(v_type_2791_);
                    crate::leanh::lean_inc(v_id_2790_);
                    crate::leanh::lean_dec(v_toRing_2768_);
                    v___x_2807_ = crate::leanh::lean_box(0);
                    v_isShared_2808_ = v_isSharedCheck_2816_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2809_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2809_, 0, v_a_2766_);
                if v_isShared_2808_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2807_, 7, v___x_2809_);
                    v___x_2811_ = v___x_2807_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2815_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_id_2790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 1, v_type_2791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 2, v_u_2792_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 3, v_ringInst_2793_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 4, v_semiringInst_2794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 5, v_charInst_x3f_2795_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 6, v_addFn_x3f_2796_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 7, v___x_2809_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 8, v_subFn_x3f_2797_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 9, v_negFn_x3f_2798_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 10, v_powFn_x3f_2799_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 11, v_intCastFn_x3f_2800_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 12, v_natCastFn_x3f_2801_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 13, v_one_x3f_2802_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 14, v_vars_2803_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 15, v_varMap_2804_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 16, v_denote_2805_);
                    v___x_2811_ = v_reuseFailAlloc_2815_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2789_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2788_, 0, v___x_2811_);
                    v___x_2813_ = v___x_2788_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2814_ = crate::leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2811_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_invFn_x3f_2769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2814_, 2, v_semiringId_x3f_2770_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2814_,
                        3,
                        v_commSemiringInst_2771_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2814_, 4, v_commRingInst_2772_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2814_,
                        5,
                        v_noZeroDivInst_x3f_2773_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2814_, 6, v_fieldInst_x3f_2774_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2814_,
                        7,
                        v_powIdentityInst_x3f_2775_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2814_, 8, v_denoteEntries_2776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2814_, 9, v_nextId_2777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2814_, 10, v_steps_2778_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2814_, 11, v_queue_2779_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2814_, 12, v_basis_2780_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2814_, 13, v_diseqs_2781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2814_, 14, v_invSet_2783_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2814_,
                        15,
                        v_powIdentityVarCount_2784_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2814_, 16, v_numEq0_x3f_2785_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2814_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_recheck_2782_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2814_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_2786_,
                    );
                    v___x_2813_ = v_reuseFailAlloc_2814_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2813_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(
    mut v___y_2830_: *mut crate::leanh::LeanObject,
    mut v___y_2831_: *mut crate::leanh::LeanObject,
    mut v___y_2832_: *mut crate::leanh::LeanObject,
    mut v___y_2833_: *mut crate::leanh::LeanObject,
    mut v___y_2834_: *mut crate::leanh::LeanObject,
    mut v___y_2835_: *mut crate::leanh::LeanObject,
    mut v___y_2836_: *mut crate::leanh::LeanObject,
    mut v___y_2837_: *mut crate::leanh::LeanObject,
    mut v___y_2838_: *mut crate::leanh::LeanObject,
    mut v___y_2839_: *mut crate::leanh::LeanObject,
    mut v___y_2840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2846_: u8 = 0;
    let mut v_toRing_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedInst_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2872_: u8 = 0;
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2876_: u8 = 0;
    let mut v_unused_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2881_: u8 = 0;
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2885_: u8 = 0;
    let mut v_isSharedCheck_2886_: u8 = 0;
    let mut v_a_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2890_: u8 = 0;
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2842_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v___y_2830_,
                    v___y_2831_,
                    v___y_2832_,
                    v___y_2833_,
                    v___y_2834_,
                    v___y_2835_,
                    v___y_2836_,
                    v___y_2837_,
                    v___y_2838_,
                    v___y_2839_,
                    v___y_2840_,
                );
                if crate::leanh::lean_obj_tag(v___x_2842_) == 0 {
                    v_a_2843_ = crate::leanh::lean_ctor_get(v___x_2842_, 0);
                    v_isSharedCheck_2886_ = (!crate::leanh::lean_is_exclusive(v___x_2842_)) as u8;
                    if v_isSharedCheck_2886_ == 0 {
                        v___x_2845_ = v___x_2842_;
                        v_isShared_2846_ = v_isSharedCheck_2886_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2843_);
                        crate::leanh::lean_dec(v___x_2842_);
                        v___x_2845_ = crate::leanh::lean_box(0);
                        v_isShared_2846_ = v_isSharedCheck_2886_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2887_ = crate::leanh::lean_ctor_get(v___x_2842_, 0);
                    v_isSharedCheck_2894_ = (!crate::leanh::lean_is_exclusive(v___x_2842_)) as u8;
                    if v_isSharedCheck_2894_ == 0 {
                        v___x_2889_ = v___x_2842_;
                        v_isShared_2890_ = v_isSharedCheck_2894_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2887_);
                        crate::leanh::lean_dec(v___x_2842_);
                        v___x_2889_ = crate::leanh::lean_box(0);
                        v_isShared_2890_ = v_isSharedCheck_2894_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_2847_ = crate::leanh::lean_ctor_get(v_a_2843_, 0);
                crate::leanh::lean_inc_ref(v_toRing_2847_);
                crate::leanh::lean_dec(v_a_2843_);
                v_mulFn_x3f_2848_ = crate::leanh::lean_ctor_get(v_toRing_2847_, 7);
                if crate::leanh::lean_obj_tag(v_mulFn_x3f_2848_) == 1 {
                    crate::leanh::lean_inc_ref(v_mulFn_x3f_2848_);
                    crate::leanh::lean_dec_ref(v_toRing_2847_);
                    v_val_2849_ = crate::leanh::lean_ctor_get(v_mulFn_x3f_2848_, 0);
                    crate::leanh::lean_inc(v_val_2849_);
                    crate::leanh::lean_dec_ref_known(v_mulFn_x3f_2848_, 1);
                    if v_isShared_2846_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2845_, 0, v_val_2849_);
                        v___x_2851_ = v___x_2845_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2852_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_val_2849_);
                        v___x_2851_ = v_reuseFailAlloc_2852_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2845_);
                    v_type_2853_ = crate::leanh::lean_ctor_get(v_toRing_2847_, 1);
                    crate::leanh::lean_inc_ref_n(v_type_2853_, 3);
                    v_u_2854_ = crate::leanh::lean_ctor_get(v_toRing_2847_, 2);
                    crate::leanh::lean_inc_n(v_u_2854_, 2);
                    v_semiringInst_2855_ = crate::leanh::lean_ctor_get(v_toRing_2847_, 4);
                    crate::leanh::lean_inc_ref(v_semiringInst_2855_);
                    crate::leanh::lean_dec_ref(v_toRing_2847_);
                    v___x_2856_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1;
                    v___x_2857_ = crate::leanh::lean_box(0);
                    v___x_2858_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2858_, 0, v_u_2854_);
                    crate::leanh::lean_ctor_set(v___x_2858_, 1, v___x_2857_);
                    crate::leanh::lean_inc_ref(v___x_2858_);
                    v___x_2859_ = l_Lean_mkConst(v___x_2856_, v___x_2858_);
                    v___x_2860_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3;
                    v___x_2861_ = l_Lean_mkConst(v___x_2860_, v___x_2858_);
                    v___x_2862_ = l_Lean_mkAppB(v___x_2861_, v_type_2853_, v_semiringInst_2855_);
                    v_expectedInst_2863_ = l_Lean_mkAppB(v___x_2859_, v_type_2853_, v___x_2862_);
                    v___x_2864_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4;
                    v___x_2865_ = l_Int_Linear_Poly_isNonlinear___redArg___closed__2;
                    v___x_2866_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_2853_, v_u_2854_, v___x_2864_, v___x_2865_, v_expectedInst_2863_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
                    if crate::leanh::lean_obj_tag(v___x_2866_) == 0 {
                        v_a_2867_ = crate::leanh::lean_ctor_get(v___x_2866_, 0);
                        crate::leanh::lean_inc_n(v_a_2867_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_2866_, 1);
                        v___f_2868_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0 as *mut core::ffi::c_void, 2, 1);
                        crate::leanh::lean_closure_set(v___f_2868_, 0, v_a_2867_);
                        v___x_2869_ =
                            l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
                                v___f_2868_,
                                v___y_2830_,
                                v___y_2831_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_2869_) == 0 {
                            v_isSharedCheck_2876_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2869_)) as u8;
                            if v_isSharedCheck_2876_ == 0 {
                                v_unused_2877_ = crate::leanh::lean_ctor_get(v___x_2869_, 0);
                                crate::leanh::lean_dec(v_unused_2877_);
                                v___x_2871_ = v___x_2869_;
                                v_isShared_2872_ = v_isSharedCheck_2876_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2869_);
                                v___x_2871_ = crate::leanh::lean_box(0);
                                v_isShared_2872_ = v_isSharedCheck_2876_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2867_);
                            v_a_2878_ = crate::leanh::lean_ctor_get(v___x_2869_, 0);
                            v_isSharedCheck_2885_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2869_)) as u8;
                            if v_isSharedCheck_2885_ == 0 {
                                v___x_2880_ = v___x_2869_;
                                v_isShared_2881_ = v_isSharedCheck_2885_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2878_);
                                crate::leanh::lean_dec(v___x_2869_);
                                v___x_2880_ = crate::leanh::lean_box(0);
                                v_isShared_2881_ = v_isSharedCheck_2885_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        return v___x_2866_;
                    }
                }
            }
            2 => {
                return v___x_2851_;
            }
            3 => {
                if v_isShared_2872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2871_, 0, v_a_2867_);
                    v___x_2874_ = v___x_2871_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2875_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2867_);
                    v___x_2874_ = v_reuseFailAlloc_2875_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2874_;
            }
            5 => {
                if v_isShared_2881_ == 0 {
                    v___x_2883_ = v___x_2880_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2884_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
                    v___x_2883_ = v_reuseFailAlloc_2884_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2883_;
            }
            7 => {
                if v_isShared_2890_ == 0 {
                    v___x_2892_ = v___x_2889_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2893_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
                    v___x_2892_ = v_reuseFailAlloc_2893_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2892_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___boxed(
    mut v___y_2895_: *mut crate::leanh::LeanObject,
    mut v___y_2896_: *mut crate::leanh::LeanObject,
    mut v___y_2897_: *mut crate::leanh::LeanObject,
    mut v___y_2898_: *mut crate::leanh::LeanObject,
    mut v___y_2899_: *mut crate::leanh::LeanObject,
    mut v___y_2900_: *mut crate::leanh::LeanObject,
    mut v___y_2901_: *mut crate::leanh::LeanObject,
    mut v___y_2902_: *mut crate::leanh::LeanObject,
    mut v___y_2903_: *mut crate::leanh::LeanObject,
    mut v___y_2904_: *mut crate::leanh::LeanObject,
    mut v___y_2905_: *mut crate::leanh::LeanObject,
    mut v___y_2906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2907_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
    crate::leanh::lean_dec(v___y_2905_);
    crate::leanh::lean_dec_ref(v___y_2904_);
    crate::leanh::lean_dec(v___y_2903_);
    crate::leanh::lean_dec_ref(v___y_2902_);
    crate::leanh::lean_dec(v___y_2901_);
    crate::leanh::lean_dec_ref(v___y_2900_);
    crate::leanh::lean_dec(v___y_2899_);
    crate::leanh::lean_dec_ref(v___y_2898_);
    crate::leanh::lean_dec(v___y_2897_);
    crate::leanh::lean_dec(v___y_2896_);
    crate::leanh::lean_dec_ref(v___y_2895_);
    return v_res_2907_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0(
    mut v_a_2908_: *mut crate::leanh::LeanObject,
    mut v_s_2909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_2924_: u8 = 0;
    let mut v_invSet_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_2928_: u8 = 0;
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v_id_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2950_: u8 = 0;
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2958_: u8 = 0;
    let mut v_unused_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2960_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2910_ = crate::leanh::lean_ctor_get(v_s_2909_, 0);
                v_invFn_x3f_2911_ = crate::leanh::lean_ctor_get(v_s_2909_, 1);
                v_semiringId_x3f_2912_ = crate::leanh::lean_ctor_get(v_s_2909_, 2);
                v_commSemiringInst_2913_ = crate::leanh::lean_ctor_get(v_s_2909_, 3);
                v_commRingInst_2914_ = crate::leanh::lean_ctor_get(v_s_2909_, 4);
                v_noZeroDivInst_x3f_2915_ = crate::leanh::lean_ctor_get(v_s_2909_, 5);
                v_fieldInst_x3f_2916_ = crate::leanh::lean_ctor_get(v_s_2909_, 6);
                v_powIdentityInst_x3f_2917_ = crate::leanh::lean_ctor_get(v_s_2909_, 7);
                v_denoteEntries_2918_ = crate::leanh::lean_ctor_get(v_s_2909_, 8);
                v_nextId_2919_ = crate::leanh::lean_ctor_get(v_s_2909_, 9);
                v_steps_2920_ = crate::leanh::lean_ctor_get(v_s_2909_, 10);
                v_queue_2921_ = crate::leanh::lean_ctor_get(v_s_2909_, 11);
                v_basis_2922_ = crate::leanh::lean_ctor_get(v_s_2909_, 12);
                v_diseqs_2923_ = crate::leanh::lean_ctor_get(v_s_2909_, 13);
                v_recheck_2924_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2909_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_2925_ = crate::leanh::lean_ctor_get(v_s_2909_, 14);
                v_powIdentityVarCount_2926_ = crate::leanh::lean_ctor_get(v_s_2909_, 15);
                v_numEq0_x3f_2927_ = crate::leanh::lean_ctor_get(v_s_2909_, 16);
                v_numEq0Updated_2928_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2909_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_2960_ = (!crate::leanh::lean_is_exclusive(v_s_2909_)) as u8;
                if v_isSharedCheck_2960_ == 0 {
                    v___x_2930_ = v_s_2909_;
                    v_isShared_2931_ = v_isSharedCheck_2960_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numEq0_x3f_2927_);
                    crate::leanh::lean_inc(v_powIdentityVarCount_2926_);
                    crate::leanh::lean_inc(v_invSet_2925_);
                    crate::leanh::lean_inc(v_diseqs_2923_);
                    crate::leanh::lean_inc(v_basis_2922_);
                    crate::leanh::lean_inc(v_queue_2921_);
                    crate::leanh::lean_inc(v_steps_2920_);
                    crate::leanh::lean_inc(v_nextId_2919_);
                    crate::leanh::lean_inc(v_denoteEntries_2918_);
                    crate::leanh::lean_inc(v_powIdentityInst_x3f_2917_);
                    crate::leanh::lean_inc(v_fieldInst_x3f_2916_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_2915_);
                    crate::leanh::lean_inc(v_commRingInst_2914_);
                    crate::leanh::lean_inc(v_commSemiringInst_2913_);
                    crate::leanh::lean_inc(v_semiringId_x3f_2912_);
                    crate::leanh::lean_inc(v_invFn_x3f_2911_);
                    crate::leanh::lean_inc(v_toRing_2910_);
                    crate::leanh::lean_dec(v_s_2909_);
                    v___x_2930_ = crate::leanh::lean_box(0);
                    v_isShared_2931_ = v_isSharedCheck_2960_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_2932_ = crate::leanh::lean_ctor_get(v_toRing_2910_, 0);
                v_type_2933_ = crate::leanh::lean_ctor_get(v_toRing_2910_, 1);
                v_u_2934_ = crate::leanh::lean_ctor_get(v_toRing_2910_, 2);
                v_ringInst_2935_ = crate::leanh::lean_ctor_get(v_toRing_2910_, 3);
                v_semiringInst_2936_ = crate::leanh::lean_ctor_get(v_toRing_2910_, 4);
                v_charInst_x3f_2937_ = crate::leanh::lean_ctor_get(v_toRing_2910_, 5);
                v_addFn_x3f_2938_ = crate::leanh::lean_ctor_get(v_toRing_2910_, 6);
                v_mulFn_x3f_2939_ = crate::leanh::lean_ctor_get(v_toRing_2910_, 7);
                v_subFn_x3f_2940_ = crate::leanh::lean_ctor_get(v_toRing_2910_, 8);
                v_negFn_x3f_2941_ = crate::leanh::lean_ctor_get(v_toRing_2910_, 9);
                v_intCastFn_x3f_2942_ = crate::leanh::lean_ctor_get(v_toRing_2910_, 11);
                v_natCastFn_x3f_2943_ = crate::leanh::lean_ctor_get(v_toRing_2910_, 12);
                v_one_x3f_2944_ = crate::leanh::lean_ctor_get(v_toRing_2910_, 13);
                v_vars_2945_ = crate::leanh::lean_ctor_get(v_toRing_2910_, 14);
                v_varMap_2946_ = crate::leanh::lean_ctor_get(v_toRing_2910_, 15);
                v_denote_2947_ = crate::leanh::lean_ctor_get(v_toRing_2910_, 16);
                v_isSharedCheck_2958_ = (!crate::leanh::lean_is_exclusive(v_toRing_2910_)) as u8;
                if v_isSharedCheck_2958_ == 0 {
                    v_unused_2959_ = crate::leanh::lean_ctor_get(v_toRing_2910_, 10);
                    crate::leanh::lean_dec(v_unused_2959_);
                    v___x_2949_ = v_toRing_2910_;
                    v_isShared_2950_ = v_isSharedCheck_2958_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_2947_);
                    crate::leanh::lean_inc(v_varMap_2946_);
                    crate::leanh::lean_inc(v_vars_2945_);
                    crate::leanh::lean_inc(v_one_x3f_2944_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_2943_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_2942_);
                    crate::leanh::lean_inc(v_negFn_x3f_2941_);
                    crate::leanh::lean_inc(v_subFn_x3f_2940_);
                    crate::leanh::lean_inc(v_mulFn_x3f_2939_);
                    crate::leanh::lean_inc(v_addFn_x3f_2938_);
                    crate::leanh::lean_inc(v_charInst_x3f_2937_);
                    crate::leanh::lean_inc(v_semiringInst_2936_);
                    crate::leanh::lean_inc(v_ringInst_2935_);
                    crate::leanh::lean_inc(v_u_2934_);
                    crate::leanh::lean_inc(v_type_2933_);
                    crate::leanh::lean_inc(v_id_2932_);
                    crate::leanh::lean_dec(v_toRing_2910_);
                    v___x_2949_ = crate::leanh::lean_box(0);
                    v_isShared_2950_ = v_isSharedCheck_2958_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2951_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2951_, 0, v_a_2908_);
                if v_isShared_2950_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2949_, 10, v___x_2951_);
                    v___x_2953_ = v___x_2949_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2957_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_id_2932_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_type_2933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 2, v_u_2934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 3, v_ringInst_2935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 4, v_semiringInst_2936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 5, v_charInst_x3f_2937_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 6, v_addFn_x3f_2938_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 7, v_mulFn_x3f_2939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 8, v_subFn_x3f_2940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 9, v_negFn_x3f_2941_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 10, v___x_2951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 11, v_intCastFn_x3f_2942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 12, v_natCastFn_x3f_2943_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 13, v_one_x3f_2944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 14, v_vars_2945_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 15, v_varMap_2946_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 16, v_denote_2947_);
                    v___x_2953_ = v_reuseFailAlloc_2957_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2931_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2930_, 0, v___x_2953_);
                    v___x_2955_ = v___x_2930_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2956_ = crate::leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2953_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_invFn_x3f_2911_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 2, v_semiringId_x3f_2912_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2956_,
                        3,
                        v_commSemiringInst_2913_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 4, v_commRingInst_2914_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2956_,
                        5,
                        v_noZeroDivInst_x3f_2915_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 6, v_fieldInst_x3f_2916_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2956_,
                        7,
                        v_powIdentityInst_x3f_2917_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 8, v_denoteEntries_2918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 9, v_nextId_2919_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 10, v_steps_2920_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 11, v_queue_2921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 12, v_basis_2922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 13, v_diseqs_2923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 14, v_invSet_2925_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2956_,
                        15,
                        v_powIdentityVarCount_2926_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 16, v_numEq0_x3f_2927_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2956_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_recheck_2924_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2956_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_2928_,
                    );
                    v___x_2955_ = v_reuseFailAlloc_2956_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2955_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2963_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2964_ = l_Lean_Level_ofNat(v___x_2963_);
    return v___x_2964_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(
    mut v_u_2971_: *mut crate::leanh::LeanObject,
    mut v_type_2972_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_2973_: *mut crate::leanh::LeanObject,
    mut v___y_2974_: *mut crate::leanh::LeanObject,
    mut v___y_2975_: *mut crate::leanh::LeanObject,
    mut v___y_2976_: *mut crate::leanh::LeanObject,
    mut v___y_2977_: *mut crate::leanh::LeanObject,
    mut v___y_2978_: *mut crate::leanh::LeanObject,
    mut v___y_2979_: *mut crate::leanh::LeanObject,
    mut v___y_2980_: *mut crate::leanh::LeanObject,
    mut v___y_2981_: *mut crate::leanh::LeanObject,
    mut v___y_2982_: *mut crate::leanh::LeanObject,
    mut v___y_2983_: *mut crate::leanh::LeanObject,
    mut v___y_2984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3010_: u8 = 0;
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2986_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0;
                v___x_2987_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1_once), _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1);
                v___x_2988_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_u_2971_);
                v___x_2989_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2989_, 0, v_u_2971_);
                crate::leanh::lean_ctor_set(v___x_2989_, 1, v___x_2988_);
                crate::leanh::lean_inc_ref(v___x_2989_);
                v___x_2990_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2990_, 0, v___x_2987_);
                crate::leanh::lean_ctor_set(v___x_2990_, 1, v___x_2989_);
                v___x_2991_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2991_, 0, v_u_2971_);
                crate::leanh::lean_ctor_set(v___x_2991_, 1, v___x_2990_);
                crate::leanh::lean_inc_ref(v___x_2991_);
                v___x_2992_ = l_Lean_mkConst(v___x_2986_, v___x_2991_);
                v___x_2993_ = l_Lean_Nat_mkType;
                crate::leanh::lean_inc_ref_n(v_type_2972_, 2);
                v___x_2994_ = l_Lean_mkApp3(v___x_2992_, v_type_2972_, v___x_2993_, v_type_2972_);
                v___x_2995_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_2994_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
                if crate::leanh::lean_obj_tag(v___x_2995_) == 0 {
                    v_a_2996_ = crate::leanh::lean_ctor_get(v___x_2995_, 0);
                    crate::leanh::lean_inc_n(v_a_2996_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2995_, 1);
                    v___x_2997_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3;
                    v___x_2998_ = l_Lean_mkConst(v___x_2997_, v___x_2989_);
                    crate::leanh::lean_inc_ref(v_type_2972_);
                    v_inst_x27_2999_ =
                        l_Lean_mkAppB(v___x_2998_, v_type_2972_, v_semiringInst_2973_);
                    v___x_3000_ = l_Int_Linear_Poly_isNonlinear___redArg___closed__5;
                    v___x_3001_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
                        v___x_3000_,
                        v_a_2996_,
                        v_inst_x27_2999_,
                        v___y_2981_,
                        v___y_2982_,
                        v___y_2983_,
                        v___y_2984_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3001_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3001_, 1);
                        v___x_3002_ = l_Lean_mkConst(v___x_3000_, v___x_2991_);
                        crate::leanh::lean_inc_ref(v_type_2972_);
                        v___x_3003_ = l_Lean_mkApp4(
                            v___x_3002_,
                            v_type_2972_,
                            v___x_2993_,
                            v_type_2972_,
                            v_a_2996_,
                        );
                        v___x_3004_ = l_Lean_Meta_Sym_canon(
                            v___x_3003_,
                            v___y_2979_,
                            v___y_2980_,
                            v___y_2981_,
                            v___y_2982_,
                            v___y_2983_,
                            v___y_2984_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3004_) == 0 {
                            v_a_3005_ = crate::leanh::lean_ctor_get(v___x_3004_, 0);
                            crate::leanh::lean_inc(v_a_3005_);
                            crate::leanh::lean_dec_ref_known(v___x_3004_, 1);
                            v___x_3006_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_3005_, v___y_2980_);
                            return v___x_3006_;
                        } else {
                            return v___x_3004_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2996_);
                        crate::leanh::lean_dec_ref_known(v___x_2991_, 2);
                        crate::leanh::lean_dec_ref(v_type_2972_);
                        v_a_3007_ = crate::leanh::lean_ctor_get(v___x_3001_, 0);
                        v_isSharedCheck_3014_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3001_)) as u8;
                        if v_isSharedCheck_3014_ == 0 {
                            v___x_3009_ = v___x_3001_;
                            v_isShared_3010_ = v_isSharedCheck_3014_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3007_);
                            crate::leanh::lean_dec(v___x_3001_);
                            v___x_3009_ = crate::leanh::lean_box(0);
                            v_isShared_3010_ = v_isSharedCheck_3014_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2991_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2989_, 2);
                    crate::leanh::lean_dec_ref(v_semiringInst_2973_);
                    crate::leanh::lean_dec_ref(v_type_2972_);
                    return v___x_2995_;
                }
            }
            1 => {
                if v_isShared_3010_ == 0 {
                    v___x_3012_ = v___x_3009_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3013_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
                    v___x_3012_ = v_reuseFailAlloc_3013_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3012_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___boxed(
    mut v_u_3015_: *mut crate::leanh::LeanObject,
    mut v_type_3016_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_3017_: *mut crate::leanh::LeanObject,
    mut v___y_3018_: *mut crate::leanh::LeanObject,
    mut v___y_3019_: *mut crate::leanh::LeanObject,
    mut v___y_3020_: *mut crate::leanh::LeanObject,
    mut v___y_3021_: *mut crate::leanh::LeanObject,
    mut v___y_3022_: *mut crate::leanh::LeanObject,
    mut v___y_3023_: *mut crate::leanh::LeanObject,
    mut v___y_3024_: *mut crate::leanh::LeanObject,
    mut v___y_3025_: *mut crate::leanh::LeanObject,
    mut v___y_3026_: *mut crate::leanh::LeanObject,
    mut v___y_3027_: *mut crate::leanh::LeanObject,
    mut v___y_3028_: *mut crate::leanh::LeanObject,
    mut v___y_3029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3030_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_3015_, v_type_3016_, v_semiringInst_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
    crate::leanh::lean_dec(v___y_3028_);
    crate::leanh::lean_dec_ref(v___y_3027_);
    crate::leanh::lean_dec(v___y_3026_);
    crate::leanh::lean_dec_ref(v___y_3025_);
    crate::leanh::lean_dec(v___y_3024_);
    crate::leanh::lean_dec_ref(v___y_3023_);
    crate::leanh::lean_dec(v___y_3022_);
    crate::leanh::lean_dec_ref(v___y_3021_);
    crate::leanh::lean_dec(v___y_3020_);
    crate::leanh::lean_dec(v___y_3019_);
    crate::leanh::lean_dec_ref(v___y_3018_);
    return v_res_3030_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(
    mut v___y_3031_: *mut crate::leanh::LeanObject,
    mut v___y_3032_: *mut crate::leanh::LeanObject,
    mut v___y_3033_: *mut crate::leanh::LeanObject,
    mut v___y_3034_: *mut crate::leanh::LeanObject,
    mut v___y_3035_: *mut crate::leanh::LeanObject,
    mut v___y_3036_: *mut crate::leanh::LeanObject,
    mut v___y_3037_: *mut crate::leanh::LeanObject,
    mut v___y_3038_: *mut crate::leanh::LeanObject,
    mut v___y_3039_: *mut crate::leanh::LeanObject,
    mut v___y_3040_: *mut crate::leanh::LeanObject,
    mut v___y_3041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3047_: u8 = 0;
    let mut v_toRing_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3063_: u8 = 0;
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3067_: u8 = 0;
    let mut v_unused_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3072_: u8 = 0;
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3076_: u8 = 0;
    let mut v_isSharedCheck_3077_: u8 = 0;
    let mut v_a_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3081_: u8 = 0;
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3043_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v___y_3031_,
                    v___y_3032_,
                    v___y_3033_,
                    v___y_3034_,
                    v___y_3035_,
                    v___y_3036_,
                    v___y_3037_,
                    v___y_3038_,
                    v___y_3039_,
                    v___y_3040_,
                    v___y_3041_,
                );
                if crate::leanh::lean_obj_tag(v___x_3043_) == 0 {
                    v_a_3044_ = crate::leanh::lean_ctor_get(v___x_3043_, 0);
                    v_isSharedCheck_3077_ = (!crate::leanh::lean_is_exclusive(v___x_3043_)) as u8;
                    if v_isSharedCheck_3077_ == 0 {
                        v___x_3046_ = v___x_3043_;
                        v_isShared_3047_ = v_isSharedCheck_3077_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3044_);
                        crate::leanh::lean_dec(v___x_3043_);
                        v___x_3046_ = crate::leanh::lean_box(0);
                        v_isShared_3047_ = v_isSharedCheck_3077_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3078_ = crate::leanh::lean_ctor_get(v___x_3043_, 0);
                    v_isSharedCheck_3085_ = (!crate::leanh::lean_is_exclusive(v___x_3043_)) as u8;
                    if v_isSharedCheck_3085_ == 0 {
                        v___x_3080_ = v___x_3043_;
                        v_isShared_3081_ = v_isSharedCheck_3085_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3078_);
                        crate::leanh::lean_dec(v___x_3043_);
                        v___x_3080_ = crate::leanh::lean_box(0);
                        v_isShared_3081_ = v_isSharedCheck_3085_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_3048_ = crate::leanh::lean_ctor_get(v_a_3044_, 0);
                crate::leanh::lean_inc_ref(v_toRing_3048_);
                crate::leanh::lean_dec(v_a_3044_);
                v_powFn_x3f_3049_ = crate::leanh::lean_ctor_get(v_toRing_3048_, 10);
                if crate::leanh::lean_obj_tag(v_powFn_x3f_3049_) == 1 {
                    crate::leanh::lean_inc_ref(v_powFn_x3f_3049_);
                    crate::leanh::lean_dec_ref(v_toRing_3048_);
                    v_val_3050_ = crate::leanh::lean_ctor_get(v_powFn_x3f_3049_, 0);
                    crate::leanh::lean_inc(v_val_3050_);
                    crate::leanh::lean_dec_ref_known(v_powFn_x3f_3049_, 1);
                    if v_isShared_3047_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3046_, 0, v_val_3050_);
                        v___x_3052_ = v___x_3046_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3053_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_val_3050_);
                        v___x_3052_ = v_reuseFailAlloc_3053_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3046_);
                    v_type_3054_ = crate::leanh::lean_ctor_get(v_toRing_3048_, 1);
                    crate::leanh::lean_inc_ref(v_type_3054_);
                    v_u_3055_ = crate::leanh::lean_ctor_get(v_toRing_3048_, 2);
                    crate::leanh::lean_inc(v_u_3055_);
                    v_semiringInst_3056_ = crate::leanh::lean_ctor_get(v_toRing_3048_, 4);
                    crate::leanh::lean_inc_ref(v_semiringInst_3056_);
                    crate::leanh::lean_dec_ref(v_toRing_3048_);
                    v___x_3057_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_3055_, v_type_3054_, v_semiringInst_3056_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
                    if crate::leanh::lean_obj_tag(v___x_3057_) == 0 {
                        v_a_3058_ = crate::leanh::lean_ctor_get(v___x_3057_, 0);
                        crate::leanh::lean_inc_n(v_a_3058_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_3057_, 1);
                        v___f_3059_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0 as *mut core::ffi::c_void, 2, 1);
                        crate::leanh::lean_closure_set(v___f_3059_, 0, v_a_3058_);
                        v___x_3060_ =
                            l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
                                v___f_3059_,
                                v___y_3031_,
                                v___y_3032_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_3060_) == 0 {
                            v_isSharedCheck_3067_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3060_)) as u8;
                            if v_isSharedCheck_3067_ == 0 {
                                v_unused_3068_ = crate::leanh::lean_ctor_get(v___x_3060_, 0);
                                crate::leanh::lean_dec(v_unused_3068_);
                                v___x_3062_ = v___x_3060_;
                                v_isShared_3063_ = v_isSharedCheck_3067_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3060_);
                                v___x_3062_ = crate::leanh::lean_box(0);
                                v_isShared_3063_ = v_isSharedCheck_3067_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3058_);
                            v_a_3069_ = crate::leanh::lean_ctor_get(v___x_3060_, 0);
                            v_isSharedCheck_3076_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3060_)) as u8;
                            if v_isSharedCheck_3076_ == 0 {
                                v___x_3071_ = v___x_3060_;
                                v_isShared_3072_ = v_isSharedCheck_3076_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3069_);
                                crate::leanh::lean_dec(v___x_3060_);
                                v___x_3071_ = crate::leanh::lean_box(0);
                                v_isShared_3072_ = v_isSharedCheck_3076_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        return v___x_3057_;
                    }
                }
            }
            2 => {
                return v___x_3052_;
            }
            3 => {
                if v_isShared_3063_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3062_, 0, v_a_3058_);
                    v___x_3065_ = v___x_3062_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3066_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3058_);
                    v___x_3065_ = v_reuseFailAlloc_3066_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3065_;
            }
            5 => {
                if v_isShared_3072_ == 0 {
                    v___x_3074_ = v___x_3071_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3075_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
                    v___x_3074_ = v_reuseFailAlloc_3075_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3074_;
            }
            7 => {
                if v_isShared_3081_ == 0 {
                    v___x_3083_ = v___x_3080_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3084_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
                    v___x_3083_ = v_reuseFailAlloc_3084_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___boxed(
    mut v___y_3086_: *mut crate::leanh::LeanObject,
    mut v___y_3087_: *mut crate::leanh::LeanObject,
    mut v___y_3088_: *mut crate::leanh::LeanObject,
    mut v___y_3089_: *mut crate::leanh::LeanObject,
    mut v___y_3090_: *mut crate::leanh::LeanObject,
    mut v___y_3091_: *mut crate::leanh::LeanObject,
    mut v___y_3092_: *mut crate::leanh::LeanObject,
    mut v___y_3093_: *mut crate::leanh::LeanObject,
    mut v___y_3094_: *mut crate::leanh::LeanObject,
    mut v___y_3095_: *mut crate::leanh::LeanObject,
    mut v___y_3096_: *mut crate::leanh::LeanObject,
    mut v___y_3097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3098_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
    crate::leanh::lean_dec(v___y_3096_);
    crate::leanh::lean_dec_ref(v___y_3095_);
    crate::leanh::lean_dec(v___y_3094_);
    crate::leanh::lean_dec_ref(v___y_3093_);
    crate::leanh::lean_dec(v___y_3092_);
    crate::leanh::lean_dec_ref(v___y_3091_);
    crate::leanh::lean_dec(v___y_3090_);
    crate::leanh::lean_dec_ref(v___y_3089_);
    crate::leanh::lean_dec(v___y_3088_);
    crate::leanh::lean_dec(v___y_3087_);
    crate::leanh::lean_dec_ref(v___y_3086_);
    return v_res_3098_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(
    mut v_pw_3099_: *mut crate::leanh::LeanObject,
    mut v___y_3100_: *mut crate::leanh::LeanObject,
    mut v___y_3101_: *mut crate::leanh::LeanObject,
    mut v___y_3102_: *mut crate::leanh::LeanObject,
    mut v___y_3103_: *mut crate::leanh::LeanObject,
    mut v___y_3104_: *mut crate::leanh::LeanObject,
    mut v___y_3105_: *mut crate::leanh::LeanObject,
    mut v___y_3106_: *mut crate::leanh::LeanObject,
    mut v___y_3107_: *mut crate::leanh::LeanObject,
    mut v___y_3108_: *mut crate::leanh::LeanObject,
    mut v___y_3109_: *mut crate::leanh::LeanObject,
    mut v___y_3110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3116_: u8 = 0;
    let mut v_toRing_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: u8 = 0;
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3129_: u8 = 0;
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3135_: u8 = 0;
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: u8 = 0;
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3144_: u8 = 0;
    let mut v_a_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3148_: u8 = 0;
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3152_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3112_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v___y_3100_,
                    v___y_3101_,
                    v___y_3102_,
                    v___y_3103_,
                    v___y_3104_,
                    v___y_3105_,
                    v___y_3106_,
                    v___y_3107_,
                    v___y_3108_,
                    v___y_3109_,
                    v___y_3110_,
                );
                if crate::leanh::lean_obj_tag(v___x_3112_) == 0 {
                    v_a_3113_ = crate::leanh::lean_ctor_get(v___x_3112_, 0);
                    v_isSharedCheck_3144_ = (!crate::leanh::lean_is_exclusive(v___x_3112_)) as u8;
                    if v_isSharedCheck_3144_ == 0 {
                        v___x_3115_ = v___x_3112_;
                        v_isShared_3116_ = v_isSharedCheck_3144_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3113_);
                        crate::leanh::lean_dec(v___x_3112_);
                        v___x_3115_ = crate::leanh::lean_box(0);
                        v_isShared_3116_ = v_isSharedCheck_3144_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_pw_3099_);
                    v_a_3145_ = crate::leanh::lean_ctor_get(v___x_3112_, 0);
                    v_isSharedCheck_3152_ = (!crate::leanh::lean_is_exclusive(v___x_3112_)) as u8;
                    if v_isSharedCheck_3152_ == 0 {
                        v___x_3147_ = v___x_3112_;
                        v_isShared_3148_ = v_isSharedCheck_3152_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3145_);
                        crate::leanh::lean_dec(v___x_3112_);
                        v___x_3147_ = crate::leanh::lean_box(0);
                        v_isShared_3148_ = v_isSharedCheck_3152_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_3117_ = crate::leanh::lean_ctor_get(v_a_3113_, 0);
                crate::leanh::lean_inc_ref(v_toRing_3117_);
                crate::leanh::lean_dec(v_a_3113_);
                v_vars_3118_ = crate::leanh::lean_ctor_get(v_toRing_3117_, 14);
                crate::leanh::lean_inc_ref(v_vars_3118_);
                crate::leanh::lean_dec_ref(v_toRing_3117_);
                v_x_3119_ = crate::leanh::lean_ctor_get(v_pw_3099_, 0);
                crate::leanh::lean_inc(v_x_3119_);
                v_k_3120_ = crate::leanh::lean_ctor_get(v_pw_3099_, 1);
                crate::leanh::lean_inc(v_k_3120_);
                crate::leanh::lean_dec_ref(v_pw_3099_);
                v_size_3139_ = crate::leanh::lean_ctor_get(v_vars_3118_, 2);
                v___x_3140_ = l_Lean_instInhabitedExpr;
                v___x_3141_ = lean_nat_dec_lt(v_x_3119_, v_size_3139_);
                if v___x_3141_ == 0 {
                    crate::leanh::lean_dec(v_x_3119_);
                    crate::leanh::lean_dec_ref(v_vars_3118_);
                    v___x_3142_ = l_outOfBounds___redArg(v___x_3140_);
                    v___y_3122_ = v___x_3142_;
                    state = 2;
                    continue;
                } else {
                    v___x_3143_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_3140_,
                        v_vars_3118_,
                        v_x_3119_,
                    );
                    crate::leanh::lean_dec(v_x_3119_);
                    crate::leanh::lean_dec_ref(v_vars_3118_);
                    v___y_3122_ = v___x_3143_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3123_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3124_ = lean_nat_dec_eq(v_k_3120_, v___x_3123_);
                if v___x_3124_ == 0 {
                    crate::leanh::lean_del_object(v___x_3115_);
                    v___x_3125_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
                    if crate::leanh::lean_obj_tag(v___x_3125_) == 0 {
                        v_a_3126_ = crate::leanh::lean_ctor_get(v___x_3125_, 0);
                        v_isSharedCheck_3135_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3125_)) as u8;
                        if v_isSharedCheck_3135_ == 0 {
                            v___x_3128_ = v___x_3125_;
                            v_isShared_3129_ = v_isSharedCheck_3135_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3126_);
                            crate::leanh::lean_dec(v___x_3125_);
                            v___x_3128_ = crate::leanh::lean_box(0);
                            v_isShared_3129_ = v_isSharedCheck_3135_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_3122_);
                        crate::leanh::lean_dec(v_k_3120_);
                        return v___x_3125_;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_3120_);
                    if v_isShared_3116_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3115_, 0, v___y_3122_);
                        v___x_3137_ = v___x_3115_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3138_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___y_3122_);
                        v___x_3137_ = v_reuseFailAlloc_3138_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3130_ = l_Lean_mkNatLit(v_k_3120_);
                v___x_3131_ = l_Lean_mkAppB(v_a_3126_, v___y_3122_, v___x_3130_);
                if v_isShared_3129_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3128_, 0, v___x_3131_);
                    v___x_3133_ = v___x_3128_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3131_);
                    v___x_3133_ = v_reuseFailAlloc_3134_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3133_;
            }
            5 => {
                return v___x_3137_;
            }
            6 => {
                if v_isShared_3148_ == 0 {
                    v___x_3150_ = v___x_3147_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3151_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
                    v___x_3150_ = v_reuseFailAlloc_3151_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3150_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9___boxed(
    mut v_pw_3153_: *mut crate::leanh::LeanObject,
    mut v___y_3154_: *mut crate::leanh::LeanObject,
    mut v___y_3155_: *mut crate::leanh::LeanObject,
    mut v___y_3156_: *mut crate::leanh::LeanObject,
    mut v___y_3157_: *mut crate::leanh::LeanObject,
    mut v___y_3158_: *mut crate::leanh::LeanObject,
    mut v___y_3159_: *mut crate::leanh::LeanObject,
    mut v___y_3160_: *mut crate::leanh::LeanObject,
    mut v___y_3161_: *mut crate::leanh::LeanObject,
    mut v___y_3162_: *mut crate::leanh::LeanObject,
    mut v___y_3163_: *mut crate::leanh::LeanObject,
    mut v___y_3164_: *mut crate::leanh::LeanObject,
    mut v___y_3165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3166_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_pw_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
    crate::leanh::lean_dec(v___y_3164_);
    crate::leanh::lean_dec_ref(v___y_3163_);
    crate::leanh::lean_dec(v___y_3162_);
    crate::leanh::lean_dec_ref(v___y_3161_);
    crate::leanh::lean_dec(v___y_3160_);
    crate::leanh::lean_dec_ref(v___y_3159_);
    crate::leanh::lean_dec(v___y_3158_);
    crate::leanh::lean_dec_ref(v___y_3157_);
    crate::leanh::lean_dec(v___y_3156_);
    crate::leanh::lean_dec(v___y_3155_);
    crate::leanh::lean_dec_ref(v___y_3154_);
    return v_res_3166_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(
    mut v_m_3167_: *mut crate::leanh::LeanObject,
    mut v_acc_3168_: *mut crate::leanh::LeanObject,
    mut v___y_3169_: *mut crate::leanh::LeanObject,
    mut v___y_3170_: *mut crate::leanh::LeanObject,
    mut v___y_3171_: *mut crate::leanh::LeanObject,
    mut v___y_3172_: *mut crate::leanh::LeanObject,
    mut v___y_3173_: *mut crate::leanh::LeanObject,
    mut v___y_3174_: *mut crate::leanh::LeanObject,
    mut v___y_3175_: *mut crate::leanh::LeanObject,
    mut v___y_3176_: *mut crate::leanh::LeanObject,
    mut v___y_3177_: *mut crate::leanh::LeanObject,
    mut v___y_3178_: *mut crate::leanh::LeanObject,
    mut v___y_3179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_m_3167_) == 0 {
                    v___x_3181_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3181_, 0, v_acc_3168_);
                    return v___x_3181_;
                } else {
                    v_p_3182_ = crate::leanh::lean_ctor_get(v_m_3167_, 0);
                    crate::leanh::lean_inc_ref(v_p_3182_);
                    v_m_3183_ = crate::leanh::lean_ctor_get(v_m_3167_, 1);
                    crate::leanh::lean_inc(v_m_3183_);
                    crate::leanh::lean_dec_ref_known(v_m_3167_, 2);
                    v___x_3184_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
                    if crate::leanh::lean_obj_tag(v___x_3184_) == 0 {
                        v_a_3185_ = crate::leanh::lean_ctor_get(v___x_3184_, 0);
                        crate::leanh::lean_inc(v_a_3185_);
                        crate::leanh::lean_dec_ref_known(v___x_3184_, 1);
                        v___x_3186_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_3182_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
                        if crate::leanh::lean_obj_tag(v___x_3186_) == 0 {
                            v_a_3187_ = crate::leanh::lean_ctor_get(v___x_3186_, 0);
                            crate::leanh::lean_inc(v_a_3187_);
                            crate::leanh::lean_dec_ref_known(v___x_3186_, 1);
                            v___x_3188_ = l_Lean_mkAppB(v_a_3185_, v_acc_3168_, v_a_3187_);
                            v_m_3167_ = v_m_3183_;
                            v_acc_3168_ = v___x_3188_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_3185_);
                            crate::leanh::lean_dec(v_m_3183_);
                            crate::leanh::lean_dec_ref(v_acc_3168_);
                            return v___x_3186_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_m_3183_);
                        crate::leanh::lean_dec_ref(v_p_3182_);
                        crate::leanh::lean_dec_ref(v_acc_3168_);
                        return v___x_3184_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10___boxed(
    mut v_m_3190_: *mut crate::leanh::LeanObject,
    mut v_acc_3191_: *mut crate::leanh::LeanObject,
    mut v___y_3192_: *mut crate::leanh::LeanObject,
    mut v___y_3193_: *mut crate::leanh::LeanObject,
    mut v___y_3194_: *mut crate::leanh::LeanObject,
    mut v___y_3195_: *mut crate::leanh::LeanObject,
    mut v___y_3196_: *mut crate::leanh::LeanObject,
    mut v___y_3197_: *mut crate::leanh::LeanObject,
    mut v___y_3198_: *mut crate::leanh::LeanObject,
    mut v___y_3199_: *mut crate::leanh::LeanObject,
    mut v___y_3200_: *mut crate::leanh::LeanObject,
    mut v___y_3201_: *mut crate::leanh::LeanObject,
    mut v___y_3202_: *mut crate::leanh::LeanObject,
    mut v___y_3203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3204_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_m_3190_, v_acc_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
    crate::leanh::lean_dec(v___y_3202_);
    crate::leanh::lean_dec_ref(v___y_3201_);
    crate::leanh::lean_dec(v___y_3200_);
    crate::leanh::lean_dec_ref(v___y_3199_);
    crate::leanh::lean_dec(v___y_3198_);
    crate::leanh::lean_dec_ref(v___y_3197_);
    crate::leanh::lean_dec(v___y_3196_);
    crate::leanh::lean_dec_ref(v___y_3195_);
    crate::leanh::lean_dec(v___y_3194_);
    crate::leanh::lean_dec(v___y_3193_);
    crate::leanh::lean_dec_ref(v___y_3192_);
    return v_res_3204_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3205_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3206_ = lean_nat_to_int(v___x_3205_);
    return v___x_3206_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(
    mut v_m_3207_: *mut crate::leanh::LeanObject,
    mut v___y_3208_: *mut crate::leanh::LeanObject,
    mut v___y_3209_: *mut crate::leanh::LeanObject,
    mut v___y_3210_: *mut crate::leanh::LeanObject,
    mut v___y_3211_: *mut crate::leanh::LeanObject,
    mut v___y_3212_: *mut crate::leanh::LeanObject,
    mut v___y_3213_: *mut crate::leanh::LeanObject,
    mut v___y_3214_: *mut crate::leanh::LeanObject,
    mut v___y_3215_: *mut crate::leanh::LeanObject,
    mut v___y_3216_: *mut crate::leanh::LeanObject,
    mut v___y_3217_: *mut crate::leanh::LeanObject,
    mut v___y_3218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_m_3207_) == 0 {
        let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3220_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0), core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once), _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
        v___x_3221_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v___x_3220_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
        return v___x_3221_;
    } else {
        let mut v_p_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_m_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_p_3222_ = crate::leanh::lean_ctor_get(v_m_3207_, 0);
        crate::leanh::lean_inc_ref(v_p_3222_);
        v_m_3223_ = crate::leanh::lean_ctor_get(v_m_3207_, 1);
        crate::leanh::lean_inc(v_m_3223_);
        crate::leanh::lean_dec_ref_known(v_m_3207_, 2);
        v___x_3224_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_3222_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
        if crate::leanh::lean_obj_tag(v___x_3224_) == 0 {
            let mut v_a_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_3225_ = crate::leanh::lean_ctor_get(v___x_3224_, 0);
            crate::leanh::lean_inc(v_a_3225_);
            crate::leanh::lean_dec_ref_known(v___x_3224_, 1);
            v___x_3226_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_m_3223_, v_a_3225_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
            return v___x_3226_;
        } else {
            crate::leanh::lean_dec(v_m_3223_);
            return v___x_3224_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___boxed(
    mut v_m_3227_: *mut crate::leanh::LeanObject,
    mut v___y_3228_: *mut crate::leanh::LeanObject,
    mut v___y_3229_: *mut crate::leanh::LeanObject,
    mut v___y_3230_: *mut crate::leanh::LeanObject,
    mut v___y_3231_: *mut crate::leanh::LeanObject,
    mut v___y_3232_: *mut crate::leanh::LeanObject,
    mut v___y_3233_: *mut crate::leanh::LeanObject,
    mut v___y_3234_: *mut crate::leanh::LeanObject,
    mut v___y_3235_: *mut crate::leanh::LeanObject,
    mut v___y_3236_: *mut crate::leanh::LeanObject,
    mut v___y_3237_: *mut crate::leanh::LeanObject,
    mut v___y_3238_: *mut crate::leanh::LeanObject,
    mut v___y_3239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3240_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_m_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
    crate::leanh::lean_dec(v___y_3238_);
    crate::leanh::lean_dec_ref(v___y_3237_);
    crate::leanh::lean_dec(v___y_3236_);
    crate::leanh::lean_dec_ref(v___y_3235_);
    crate::leanh::lean_dec(v___y_3234_);
    crate::leanh::lean_dec_ref(v___y_3233_);
    crate::leanh::lean_dec(v___y_3232_);
    crate::leanh::lean_dec_ref(v___y_3231_);
    crate::leanh::lean_dec(v___y_3230_);
    crate::leanh::lean_dec(v___y_3229_);
    crate::leanh::lean_dec_ref(v___y_3228_);
    return v_res_3240_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1(
    mut v_k_3241_: *mut crate::leanh::LeanObject,
    mut v_m_3242_: *mut crate::leanh::LeanObject,
    mut v___y_3243_: *mut crate::leanh::LeanObject,
    mut v___y_3244_: *mut crate::leanh::LeanObject,
    mut v___y_3245_: *mut crate::leanh::LeanObject,
    mut v___y_3246_: *mut crate::leanh::LeanObject,
    mut v___y_3247_: *mut crate::leanh::LeanObject,
    mut v___y_3248_: *mut crate::leanh::LeanObject,
    mut v___y_3249_: *mut crate::leanh::LeanObject,
    mut v___y_3250_: *mut crate::leanh::LeanObject,
    mut v___y_3251_: *mut crate::leanh::LeanObject,
    mut v___y_3252_: *mut crate::leanh::LeanObject,
    mut v___y_3253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: u8 = 0;
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3265_: u8 = 0;
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3270_: u8 = 0;
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3255_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0), core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once), _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
                v___x_3256_ = lean_int_dec_eq(v_k_3241_, v___x_3255_);
                if v___x_3256_ == 0 {
                    v___x_3257_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
                    if crate::leanh::lean_obj_tag(v___x_3257_) == 0 {
                        v_a_3258_ = crate::leanh::lean_ctor_get(v___x_3257_, 0);
                        crate::leanh::lean_inc(v_a_3258_);
                        crate::leanh::lean_dec_ref_known(v___x_3257_, 1);
                        v___x_3259_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_3241_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
                        if crate::leanh::lean_obj_tag(v___x_3259_) == 0 {
                            v_a_3260_ = crate::leanh::lean_ctor_get(v___x_3259_, 0);
                            crate::leanh::lean_inc(v_a_3260_);
                            crate::leanh::lean_dec_ref_known(v___x_3259_, 1);
                            v___x_3261_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_m_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
                            if crate::leanh::lean_obj_tag(v___x_3261_) == 0 {
                                v_a_3262_ = crate::leanh::lean_ctor_get(v___x_3261_, 0);
                                v_isSharedCheck_3270_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3261_)) as u8;
                                if v_isSharedCheck_3270_ == 0 {
                                    v___x_3264_ = v___x_3261_;
                                    v_isShared_3265_ = v_isSharedCheck_3270_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3262_);
                                    crate::leanh::lean_dec(v___x_3261_);
                                    v___x_3264_ = crate::leanh::lean_box(0);
                                    v_isShared_3265_ = v_isSharedCheck_3270_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3260_);
                                crate::leanh::lean_dec(v_a_3258_);
                                return v___x_3261_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3258_);
                            crate::leanh::lean_dec(v_m_3242_);
                            return v___x_3259_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_m_3242_);
                        return v___x_3257_;
                    }
                } else {
                    v___x_3271_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_m_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
                    return v___x_3271_;
                }
            }
            1 => {
                v___x_3266_ = l_Lean_mkAppB(v_a_3258_, v_a_3260_, v_a_3262_);
                if v_isShared_3265_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3264_, 0, v___x_3266_);
                    v___x_3268_ = v___x_3264_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3269_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3266_);
                    v___x_3268_ = v_reuseFailAlloc_3269_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3268_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1___boxed(
    mut v_k_3272_: *mut crate::leanh::LeanObject,
    mut v_m_3273_: *mut crate::leanh::LeanObject,
    mut v___y_3274_: *mut crate::leanh::LeanObject,
    mut v___y_3275_: *mut crate::leanh::LeanObject,
    mut v___y_3276_: *mut crate::leanh::LeanObject,
    mut v___y_3277_: *mut crate::leanh::LeanObject,
    mut v___y_3278_: *mut crate::leanh::LeanObject,
    mut v___y_3279_: *mut crate::leanh::LeanObject,
    mut v___y_3280_: *mut crate::leanh::LeanObject,
    mut v___y_3281_: *mut crate::leanh::LeanObject,
    mut v___y_3282_: *mut crate::leanh::LeanObject,
    mut v___y_3283_: *mut crate::leanh::LeanObject,
    mut v___y_3284_: *mut crate::leanh::LeanObject,
    mut v___y_3285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3286_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_3272_, v_m_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
    crate::leanh::lean_dec(v___y_3284_);
    crate::leanh::lean_dec_ref(v___y_3283_);
    crate::leanh::lean_dec(v___y_3282_);
    crate::leanh::lean_dec_ref(v___y_3281_);
    crate::leanh::lean_dec(v___y_3280_);
    crate::leanh::lean_dec_ref(v___y_3279_);
    crate::leanh::lean_dec(v___y_3278_);
    crate::leanh::lean_dec_ref(v___y_3277_);
    crate::leanh::lean_dec(v___y_3276_);
    crate::leanh::lean_dec(v___y_3275_);
    crate::leanh::lean_dec_ref(v___y_3274_);
    crate::leanh::lean_dec(v_k_3272_);
    return v_res_3286_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2(
    mut v_p_3287_: *mut crate::leanh::LeanObject,
    mut v_acc_3288_: *mut crate::leanh::LeanObject,
    mut v___y_3289_: *mut crate::leanh::LeanObject,
    mut v___y_3290_: *mut crate::leanh::LeanObject,
    mut v___y_3291_: *mut crate::leanh::LeanObject,
    mut v___y_3292_: *mut crate::leanh::LeanObject,
    mut v___y_3293_: *mut crate::leanh::LeanObject,
    mut v___y_3294_: *mut crate::leanh::LeanObject,
    mut v___y_3295_: *mut crate::leanh::LeanObject,
    mut v___y_3296_: *mut crate::leanh::LeanObject,
    mut v___y_3297_: *mut crate::leanh::LeanObject,
    mut v___y_3298_: *mut crate::leanh::LeanObject,
    mut v___y_3299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3304_: u8 = 0;
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: u8 = 0;
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3318_: u8 = 0;
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3322_: u8 = 0;
    let mut v_k_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_3287_) == 0 {
                    v_k_3301_ = crate::leanh::lean_ctor_get(v_p_3287_, 0);
                    v_isSharedCheck_3322_ = (!crate::leanh::lean_is_exclusive(v_p_3287_)) as u8;
                    if v_isSharedCheck_3322_ == 0 {
                        v___x_3303_ = v_p_3287_;
                        v_isShared_3304_ = v_isSharedCheck_3322_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_3301_);
                        crate::leanh::lean_dec(v_p_3287_);
                        v___x_3303_ = crate::leanh::lean_box(0);
                        v_isShared_3304_ = v_isSharedCheck_3322_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_3323_ = crate::leanh::lean_ctor_get(v_p_3287_, 0);
                    crate::leanh::lean_inc(v_k_3323_);
                    v_v_3324_ = crate::leanh::lean_ctor_get(v_p_3287_, 1);
                    crate::leanh::lean_inc(v_v_3324_);
                    v_p_3325_ = crate::leanh::lean_ctor_get(v_p_3287_, 2);
                    crate::leanh::lean_inc_ref(v_p_3325_);
                    crate::leanh::lean_dec_ref_known(v_p_3287_, 3);
                    v___x_3326_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
                    if crate::leanh::lean_obj_tag(v___x_3326_) == 0 {
                        v_a_3327_ = crate::leanh::lean_ctor_get(v___x_3326_, 0);
                        crate::leanh::lean_inc(v_a_3327_);
                        crate::leanh::lean_dec_ref_known(v___x_3326_, 1);
                        v___x_3328_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_3323_, v_v_3324_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
                        crate::leanh::lean_dec(v_k_3323_);
                        if crate::leanh::lean_obj_tag(v___x_3328_) == 0 {
                            v_a_3329_ = crate::leanh::lean_ctor_get(v___x_3328_, 0);
                            crate::leanh::lean_inc(v_a_3329_);
                            crate::leanh::lean_dec_ref_known(v___x_3328_, 1);
                            v___x_3330_ = l_Lean_mkAppB(v_a_3327_, v_acc_3288_, v_a_3329_);
                            v_p_3287_ = v_p_3325_;
                            v_acc_3288_ = v___x_3330_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_3327_);
                            crate::leanh::lean_dec_ref(v_p_3325_);
                            crate::leanh::lean_dec_ref(v_acc_3288_);
                            return v___x_3328_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_p_3325_);
                        crate::leanh::lean_dec(v_v_3324_);
                        crate::leanh::lean_dec(v_k_3323_);
                        crate::leanh::lean_dec_ref(v_acc_3288_);
                        return v___x_3326_;
                    }
                }
            }
            1 => {
                v___x_3305_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once), _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
                v___x_3306_ = lean_int_dec_eq(v_k_3301_, v___x_3305_);
                if v___x_3306_ == 0 {
                    crate::leanh::lean_del_object(v___x_3303_);
                    v___x_3307_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
                    if crate::leanh::lean_obj_tag(v___x_3307_) == 0 {
                        v_a_3308_ = crate::leanh::lean_ctor_get(v___x_3307_, 0);
                        crate::leanh::lean_inc(v_a_3308_);
                        crate::leanh::lean_dec_ref_known(v___x_3307_, 1);
                        v___x_3309_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_3301_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
                        crate::leanh::lean_dec(v_k_3301_);
                        if crate::leanh::lean_obj_tag(v___x_3309_) == 0 {
                            v_a_3310_ = crate::leanh::lean_ctor_get(v___x_3309_, 0);
                            v_isSharedCheck_3318_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3309_)) as u8;
                            if v_isSharedCheck_3318_ == 0 {
                                v___x_3312_ = v___x_3309_;
                                v_isShared_3313_ = v_isSharedCheck_3318_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3310_);
                                crate::leanh::lean_dec(v___x_3309_);
                                v___x_3312_ = crate::leanh::lean_box(0);
                                v_isShared_3313_ = v_isSharedCheck_3318_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3308_);
                            crate::leanh::lean_dec_ref(v_acc_3288_);
                            return v___x_3309_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_k_3301_);
                        crate::leanh::lean_dec_ref(v_acc_3288_);
                        return v___x_3307_;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_3301_);
                    if v_isShared_3304_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3303_, 0, v_acc_3288_);
                        v___x_3320_ = v___x_3303_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3321_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_acc_3288_);
                        v___x_3320_ = v_reuseFailAlloc_3321_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3314_ = l_Lean_mkAppB(v_a_3308_, v_acc_3288_, v_a_3310_);
                if v_isShared_3313_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3312_, 0, v___x_3314_);
                    v___x_3316_ = v___x_3312_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3317_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
                    v___x_3316_ = v_reuseFailAlloc_3317_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3316_;
            }
            4 => {
                return v___x_3320_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2___boxed(
    mut v_p_3332_: *mut crate::leanh::LeanObject,
    mut v_acc_3333_: *mut crate::leanh::LeanObject,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
    mut v___y_3335_: *mut crate::leanh::LeanObject,
    mut v___y_3336_: *mut crate::leanh::LeanObject,
    mut v___y_3337_: *mut crate::leanh::LeanObject,
    mut v___y_3338_: *mut crate::leanh::LeanObject,
    mut v___y_3339_: *mut crate::leanh::LeanObject,
    mut v___y_3340_: *mut crate::leanh::LeanObject,
    mut v___y_3341_: *mut crate::leanh::LeanObject,
    mut v___y_3342_: *mut crate::leanh::LeanObject,
    mut v___y_3343_: *mut crate::leanh::LeanObject,
    mut v___y_3344_: *mut crate::leanh::LeanObject,
    mut v___y_3345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3346_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_3332_, v_acc_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
    crate::leanh::lean_dec(v___y_3344_);
    crate::leanh::lean_dec_ref(v___y_3343_);
    crate::leanh::lean_dec(v___y_3342_);
    crate::leanh::lean_dec_ref(v___y_3341_);
    crate::leanh::lean_dec(v___y_3340_);
    crate::leanh::lean_dec_ref(v___y_3339_);
    crate::leanh::lean_dec(v___y_3338_);
    crate::leanh::lean_dec_ref(v___y_3337_);
    crate::leanh::lean_dec(v___y_3336_);
    crate::leanh::lean_dec(v___y_3335_);
    crate::leanh::lean_dec_ref(v___y_3334_);
    return v_res_3346_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0(
    mut v_p_3347_: *mut crate::leanh::LeanObject,
    mut v___y_3348_: *mut crate::leanh::LeanObject,
    mut v___y_3349_: *mut crate::leanh::LeanObject,
    mut v___y_3350_: *mut crate::leanh::LeanObject,
    mut v___y_3351_: *mut crate::leanh::LeanObject,
    mut v___y_3352_: *mut crate::leanh::LeanObject,
    mut v___y_3353_: *mut crate::leanh::LeanObject,
    mut v___y_3354_: *mut crate::leanh::LeanObject,
    mut v___y_3355_: *mut crate::leanh::LeanObject,
    mut v___y_3356_: *mut crate::leanh::LeanObject,
    mut v___y_3357_: *mut crate::leanh::LeanObject,
    mut v___y_3358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_3347_) == 0 {
        let mut v_k_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_3360_ = crate::leanh::lean_ctor_get(v_p_3347_, 0);
        crate::leanh::lean_inc(v_k_3360_);
        crate::leanh::lean_dec_ref_known(v_p_3347_, 1);
        v___x_3361_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_3360_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
        crate::leanh::lean_dec(v_k_3360_);
        return v___x_3361_;
    } else {
        let mut v_k_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_3362_ = crate::leanh::lean_ctor_get(v_p_3347_, 0);
        crate::leanh::lean_inc(v_k_3362_);
        v_v_3363_ = crate::leanh::lean_ctor_get(v_p_3347_, 1);
        crate::leanh::lean_inc(v_v_3363_);
        v_p_3364_ = crate::leanh::lean_ctor_get(v_p_3347_, 2);
        crate::leanh::lean_inc_ref(v_p_3364_);
        crate::leanh::lean_dec_ref_known(v_p_3347_, 3);
        v___x_3365_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_3362_, v_v_3363_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
        crate::leanh::lean_dec(v_k_3362_);
        if crate::leanh::lean_obj_tag(v___x_3365_) == 0 {
            let mut v_a_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_3366_ = crate::leanh::lean_ctor_get(v___x_3365_, 0);
            crate::leanh::lean_inc(v_a_3366_);
            crate::leanh::lean_dec_ref_known(v___x_3365_, 1);
            v___x_3367_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_3364_, v_a_3366_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
            return v___x_3367_;
        } else {
            crate::leanh::lean_dec_ref(v_p_3364_);
            return v___x_3365_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0___boxed(
    mut v_p_3368_: *mut crate::leanh::LeanObject,
    mut v___y_3369_: *mut crate::leanh::LeanObject,
    mut v___y_3370_: *mut crate::leanh::LeanObject,
    mut v___y_3371_: *mut crate::leanh::LeanObject,
    mut v___y_3372_: *mut crate::leanh::LeanObject,
    mut v___y_3373_: *mut crate::leanh::LeanObject,
    mut v___y_3374_: *mut crate::leanh::LeanObject,
    mut v___y_3375_: *mut crate::leanh::LeanObject,
    mut v___y_3376_: *mut crate::leanh::LeanObject,
    mut v___y_3377_: *mut crate::leanh::LeanObject,
    mut v___y_3378_: *mut crate::leanh::LeanObject,
    mut v___y_3379_: *mut crate::leanh::LeanObject,
    mut v___y_3380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3381_ =
        l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0(
            v_p_3368_,
            v___y_3369_,
            v___y_3370_,
            v___y_3371_,
            v___y_3372_,
            v___y_3373_,
            v___y_3374_,
            v___y_3375_,
            v___y_3376_,
            v___y_3377_,
            v___y_3378_,
            v___y_3379_,
        );
    crate::leanh::lean_dec(v___y_3379_);
    crate::leanh::lean_dec_ref(v___y_3378_);
    crate::leanh::lean_dec(v___y_3377_);
    crate::leanh::lean_dec_ref(v___y_3376_);
    crate::leanh::lean_dec(v___y_3375_);
    crate::leanh::lean_dec_ref(v___y_3374_);
    crate::leanh::lean_dec(v___y_3373_);
    crate::leanh::lean_dec_ref(v___y_3372_);
    crate::leanh::lean_dec(v___y_3371_);
    crate::leanh::lean_dec(v___y_3370_);
    crate::leanh::lean_dec_ref(v___y_3369_);
    return v_res_3381_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0()
-> f64 {
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: f64 = 0.0;
    v___x_3382_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3383_ = lean_float_of_nat(v___x_3382_);
    return v___x_3383_;
}
pub unsafe fn l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg(
    mut v_cls_3387_: *mut crate::leanh::LeanObject,
    mut v_msg_3388_: *mut crate::leanh::LeanObject,
    mut v___y_3389_: *mut crate::leanh::LeanObject,
    mut v___y_3390_: *mut crate::leanh::LeanObject,
    mut v___y_3391_: *mut crate::leanh::LeanObject,
    mut v___y_3392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3399_: u8 = 0;
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3412_: u8 = 0;
    let mut v_tid_3413_: u64 = 0;
    let mut v_traces_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3417_: u8 = 0;
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: f64 = 0.0;
    let mut v___x_3420_: u8 = 0;
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3438_: u8 = 0;
    let mut v_isSharedCheck_3439_: u8 = 0;
    let mut v_isSharedCheck_3440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3394_ = crate::leanh::lean_ctor_get(v___y_3391_, 5);
                v___x_3395_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
                v_a_3396_ = crate::leanh::lean_ctor_get(v___x_3395_, 0);
                v_isSharedCheck_3440_ = (!crate::leanh::lean_is_exclusive(v___x_3395_)) as u8;
                if v_isSharedCheck_3440_ == 0 {
                    v___x_3398_ = v___x_3395_;
                    v_isShared_3399_ = v_isSharedCheck_3440_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3396_);
                    crate::leanh::lean_dec(v___x_3395_);
                    v___x_3398_ = crate::leanh::lean_box(0);
                    v_isShared_3399_ = v_isSharedCheck_3440_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3400_ = lean_st_ref_take(v___y_3392_);
                v_traceState_3401_ = crate::leanh::lean_ctor_get(v___x_3400_, 4);
                v_env_3402_ = crate::leanh::lean_ctor_get(v___x_3400_, 0);
                v_nextMacroScope_3403_ = crate::leanh::lean_ctor_get(v___x_3400_, 1);
                v_ngen_3404_ = crate::leanh::lean_ctor_get(v___x_3400_, 2);
                v_auxDeclNGen_3405_ = crate::leanh::lean_ctor_get(v___x_3400_, 3);
                v_cache_3406_ = crate::leanh::lean_ctor_get(v___x_3400_, 5);
                v_messages_3407_ = crate::leanh::lean_ctor_get(v___x_3400_, 6);
                v_infoState_3408_ = crate::leanh::lean_ctor_get(v___x_3400_, 7);
                v_snapshotTasks_3409_ = crate::leanh::lean_ctor_get(v___x_3400_, 8);
                v_isSharedCheck_3439_ = (!crate::leanh::lean_is_exclusive(v___x_3400_)) as u8;
                if v_isSharedCheck_3439_ == 0 {
                    v___x_3411_ = v___x_3400_;
                    v_isShared_3412_ = v_isSharedCheck_3439_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3409_);
                    crate::leanh::lean_inc(v_infoState_3408_);
                    crate::leanh::lean_inc(v_messages_3407_);
                    crate::leanh::lean_inc(v_cache_3406_);
                    crate::leanh::lean_inc(v_traceState_3401_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3405_);
                    crate::leanh::lean_inc(v_ngen_3404_);
                    crate::leanh::lean_inc(v_nextMacroScope_3403_);
                    crate::leanh::lean_inc(v_env_3402_);
                    crate::leanh::lean_dec(v___x_3400_);
                    v___x_3411_ = crate::leanh::lean_box(0);
                    v_isShared_3412_ = v_isSharedCheck_3439_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3413_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3401_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3414_ = crate::leanh::lean_ctor_get(v_traceState_3401_, 0);
                v_isSharedCheck_3438_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3401_)) as u8;
                if v_isSharedCheck_3438_ == 0 {
                    v___x_3416_ = v_traceState_3401_;
                    v_isShared_3417_ = v_isSharedCheck_3438_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3414_);
                    crate::leanh::lean_dec(v_traceState_3401_);
                    v___x_3416_ = crate::leanh::lean_box(0);
                    v_isShared_3417_ = v_isSharedCheck_3438_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3418_ = crate::leanh::lean_box(0);
                v___x_3419_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0);
                v___x_3420_ = 0;
                v___x_3421_ = l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1;
                v___x_3422_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3422_, 0, v_cls_3387_);
                crate::leanh::lean_ctor_set(v___x_3422_, 1, v___x_3418_);
                crate::leanh::lean_ctor_set(v___x_3422_, 2, v___x_3421_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3422_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3419_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3422_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3419_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3422_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3420_,
                );
                v___x_3423_ = l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2;
                v___x_3424_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3424_, 0, v___x_3422_);
                crate::leanh::lean_ctor_set(v___x_3424_, 1, v_a_3396_);
                crate::leanh::lean_ctor_set(v___x_3424_, 2, v___x_3423_);
                crate::leanh::lean_inc(v_ref_3394_);
                v___x_3425_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3425_, 0, v_ref_3394_);
                crate::leanh::lean_ctor_set(v___x_3425_, 1, v___x_3424_);
                v___x_3426_ = l_Lean_PersistentArray_push___redArg(v_traces_3414_, v___x_3425_);
                if v_isShared_3417_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3416_, 0, v___x_3426_);
                    v___x_3428_ = v___x_3416_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3437_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3426_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3437_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3413_,
                    );
                    v___x_3428_ = v_reuseFailAlloc_3437_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3412_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3411_, 4, v___x_3428_);
                    v___x_3430_ = v___x_3411_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3436_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_env_3402_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3436_, 1, v_nextMacroScope_3403_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3436_, 2, v_ngen_3404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3436_, 3, v_auxDeclNGen_3405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3436_, 4, v___x_3428_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3436_, 5, v_cache_3406_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3436_, 6, v_messages_3407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3436_, 7, v_infoState_3408_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3436_, 8, v_snapshotTasks_3409_);
                    v___x_3430_ = v_reuseFailAlloc_3436_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3431_ = lean_st_ref_set(v___y_3392_, v___x_3430_);
                v___x_3432_ = crate::leanh::lean_box(0);
                if v_isShared_3399_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3398_, 0, v___x_3432_);
                    v___x_3434_ = v___x_3398_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3435_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3432_);
                    v___x_3434_ = v_reuseFailAlloc_3435_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3434_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___boxed(
    mut v_cls_3441_: *mut crate::leanh::LeanObject,
    mut v_msg_3442_: *mut crate::leanh::LeanObject,
    mut v___y_3443_: *mut crate::leanh::LeanObject,
    mut v___y_3444_: *mut crate::leanh::LeanObject,
    mut v___y_3445_: *mut crate::leanh::LeanObject,
    mut v___y_3446_: *mut crate::leanh::LeanObject,
    mut v___y_3447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3448_ = l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg(
        v_cls_3441_,
        v_msg_3442_,
        v___y_3443_,
        v___y_3444_,
        v___y_3445_,
        v___y_3446_,
    );
    crate::leanh::lean_dec(v___y_3446_);
    crate::leanh::lean_dec_ref(v___y_3445_);
    crate::leanh::lean_dec(v___y_3444_);
    crate::leanh::lean_dec_ref(v___y_3443_);
    return v_res_3448_;
}
pub unsafe fn _init_l_Int_Linear_Poly_normCommRing_x3f___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3449_ = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
    v___x_3450_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3450_, 0, v___x_3449_);
    return v___x_3450_;
}
pub unsafe fn _init_l_Int_Linear_Poly_normCommRing_x3f___closed__8() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3463_ = l_Int_Linear_Poly_normCommRing_x3f___closed__5;
    v___x_3464_ = l_Int_Linear_Poly_normCommRing_x3f___closed__7;
    v___x_3465_ = l_Lean_Name_append(v___x_3464_, v___x_3463_);
    return v___x_3465_;
}
pub unsafe fn _init_l_Int_Linear_Poly_normCommRing_x3f___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3467_ = l_Int_Linear_Poly_normCommRing_x3f___closed__9;
    v___x_3468_ = l_Lean_stringToMessageData(v___x_3467_);
    return v___x_3468_;
}
pub unsafe fn l_Int_Linear_Poly_normCommRing_x3f(
    mut v_p_3469_: *mut crate::leanh::LeanObject,
    mut v_a_3470_: *mut crate::leanh::LeanObject,
    mut v_a_3471_: *mut crate::leanh::LeanObject,
    mut v_a_3472_: *mut crate::leanh::LeanObject,
    mut v_a_3473_: *mut crate::leanh::LeanObject,
    mut v_a_3474_: *mut crate::leanh::LeanObject,
    mut v_a_3475_: *mut crate::leanh::LeanObject,
    mut v_a_3476_: *mut crate::leanh::LeanObject,
    mut v_a_3477_: *mut crate::leanh::LeanObject,
    mut v_a_3478_: *mut crate::leanh::LeanObject,
    mut v_a_3479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3485_: u8 = 0;
    let mut v___x_3486_: u8 = 0;
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3495_: u8 = 0;
    let mut v_val_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: u8 = 0;
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: u8 = 0;
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3512_: u8 = 0;
    let mut v_val_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3518_: u8 = 0;
    let mut v_val_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3522_: u8 = 0;
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3531_: u8 = 0;
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3536_: u8 = 0;
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: u8 = 0;
    let mut v___f_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3551_: u8 = 0;
    let mut v_inheritedTraceOptions_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: u8 = 0;
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3567_: u8 = 0;
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3571_: u8 = 0;
    let mut v_a_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3575_: u8 = 0;
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3579_: u8 = 0;
    let mut v_a_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3583_: u8 = 0;
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3587_: u8 = 0;
    let mut v_a_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3591_: u8 = 0;
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3595_: u8 = 0;
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3600_: u8 = 0;
    let mut v_a_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3604_: u8 = 0;
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3608_: u8 = 0;
    let mut v_isSharedCheck_3609_: u8 = 0;
    let mut v_unused_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3614_: u8 = 0;
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3618_: u8 = 0;
    let mut v_a_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3622_: u8 = 0;
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3626_: u8 = 0;
    let mut v_a_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3630_: u8 = 0;
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3634_: u8 = 0;
    let mut v_isSharedCheck_3635_: u8 = 0;
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3640_: u8 = 0;
    let mut v_a_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3644_: u8 = 0;
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3648_: u8 = 0;
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3653_: u8 = 0;
    let mut v_a_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3657_: u8 = 0;
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3661_: u8 = 0;
    let mut v_a_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3665_: u8 = 0;
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3669_: u8 = 0;
    let mut v_a_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3673_: u8 = 0;
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3677_: u8 = 0;
    let mut v_a_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3681_: u8 = 0;
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3685_: u8 = 0;
    let mut v_a_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3689_: u8 = 0;
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3693_: u8 = 0;
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3698_: u8 = 0;
    let mut v_a_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3702_: u8 = 0;
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3706_: u8 = 0;
    let mut v_isSharedCheck_3707_: u8 = 0;
    let mut v_a_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3711_: u8 = 0;
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3715_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3481_ =
                    l_Int_Linear_Poly_isNonlinear___redArg(v_p_3469_, v_a_3470_, v_a_3478_);
                if crate::leanh::lean_obj_tag(v___x_3481_) == 0 {
                    v_a_3482_ = crate::leanh::lean_ctor_get(v___x_3481_, 0);
                    v_isSharedCheck_3707_ = (!crate::leanh::lean_is_exclusive(v___x_3481_)) as u8;
                    if v_isSharedCheck_3707_ == 0 {
                        v___x_3484_ = v___x_3481_;
                        v_isShared_3485_ = v_isSharedCheck_3707_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3482_);
                        crate::leanh::lean_dec(v___x_3481_);
                        v___x_3484_ = crate::leanh::lean_box(0);
                        v_isShared_3485_ = v_isSharedCheck_3707_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_p_3469_);
                    v_a_3708_ = crate::leanh::lean_ctor_get(v___x_3481_, 0);
                    v_isSharedCheck_3715_ = (!crate::leanh::lean_is_exclusive(v___x_3481_)) as u8;
                    if v_isSharedCheck_3715_ == 0 {
                        v___x_3710_ = v___x_3481_;
                        v_isShared_3711_ = v_isSharedCheck_3715_;
                        state = 46;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3708_);
                        crate::leanh::lean_dec(v___x_3481_);
                        v___x_3710_ = crate::leanh::lean_box(0);
                        v_isShared_3711_ = v_isSharedCheck_3715_;
                        state = 46;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3486_ = (crate::leanh::lean_unbox(v_a_3482_) as u8);
                if v___x_3486_ == 0 {
                    crate::leanh::lean_dec(v_a_3482_);
                    crate::leanh::lean_dec_ref(v_p_3469_);
                    v___x_3487_ = crate::leanh::lean_box(0);
                    if v_isShared_3485_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3484_, 0, v___x_3487_);
                        v___x_3489_ = v___x_3484_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3490_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3487_);
                        v___x_3489_ = v_reuseFailAlloc_3490_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3484_);
                    v___x_3491_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(
                        v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_,
                        v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3491_) == 0 {
                        v_a_3492_ = crate::leanh::lean_ctor_get(v___x_3491_, 0);
                        v_isSharedCheck_3698_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3491_)) as u8;
                        if v_isSharedCheck_3698_ == 0 {
                            v___x_3494_ = v___x_3491_;
                            v_isShared_3495_ = v_isSharedCheck_3698_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3492_);
                            crate::leanh::lean_dec(v___x_3491_);
                            v___x_3494_ = crate::leanh::lean_box(0);
                            v_isShared_3495_ = v_isSharedCheck_3698_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3482_);
                        crate::leanh::lean_dec_ref(v_p_3469_);
                        v_a_3699_ = crate::leanh::lean_ctor_get(v___x_3491_, 0);
                        v_isSharedCheck_3706_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3491_)) as u8;
                        if v_isSharedCheck_3706_ == 0 {
                            v___x_3701_ = v___x_3491_;
                            v_isShared_3702_ = v_isSharedCheck_3706_;
                            state = 44;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3699_);
                            crate::leanh::lean_dec(v___x_3491_);
                            v___x_3701_ = crate::leanh::lean_box(0);
                            v_isShared_3702_ = v_isSharedCheck_3706_;
                            state = 44;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3489_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_3492_) == 1 {
                    crate::leanh::lean_del_object(v___x_3494_);
                    v_val_3496_ = crate::leanh::lean_ctor_get(v_a_3492_, 0);
                    crate::leanh::lean_inc(v_val_3496_);
                    crate::leanh::lean_dec_ref_known(v_a_3492_, 1);
                    crate::leanh::lean_inc_ref(v_p_3469_);
                    v___x_3497_ =
                        l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_3469_, v_a_3470_, v_a_3478_);
                    if crate::leanh::lean_obj_tag(v___x_3497_) == 0 {
                        v_a_3498_ = crate::leanh::lean_ctor_get(v___x_3497_, 0);
                        crate::leanh::lean_inc(v_a_3498_);
                        crate::leanh::lean_dec_ref_known(v___x_3497_, 1);
                        v___x_3499_ = l_Lean_Meta_Sym_canon(
                            v_a_3498_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_,
                            v_a_3479_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3499_) == 0 {
                            v_a_3500_ = crate::leanh::lean_ctor_get(v___x_3499_, 0);
                            crate::leanh::lean_inc(v_a_3500_);
                            crate::leanh::lean_dec_ref_known(v___x_3499_, 1);
                            v___x_3501_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_3500_, v_a_3475_);
                            if crate::leanh::lean_obj_tag(v___x_3501_) == 0 {
                                v_a_3502_ = crate::leanh::lean_ctor_get(v___x_3501_, 0);
                                crate::leanh::lean_inc(v_a_3502_);
                                crate::leanh::lean_dec_ref_known(v___x_3501_, 1);
                                crate::leanh::lean_inc_ref(v_p_3469_);
                                v___x_3503_ = l_Int_Linear_Poly_getGeneration___redArg(
                                    v_p_3469_, v_a_3470_, v_a_3478_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3503_) == 0 {
                                    v_a_3504_ = crate::leanh::lean_ctor_get(v___x_3503_, 0);
                                    crate::leanh::lean_inc_n(v_a_3504_, 2);
                                    crate::leanh::lean_dec_ref_known(v___x_3503_, 1);
                                    v___x_3505_ = 0;
                                    v___x_3506_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3506_, 0, v_val_3496_);
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_3506_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                            as u32,
                                        v___x_3505_,
                                    );
                                    v___x_3507_ = (crate::leanh::lean_unbox(v_a_3482_) as u8);
                                    v___x_3508_ = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(
                                        v_a_3502_,
                                        v___x_3507_,
                                        v_a_3504_,
                                        v___x_3506_,
                                        v_a_3470_,
                                        v_a_3471_,
                                        v_a_3472_,
                                        v_a_3473_,
                                        v_a_3474_,
                                        v_a_3475_,
                                        v_a_3476_,
                                        v_a_3477_,
                                        v_a_3478_,
                                        v_a_3479_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_3508_) == 0 {
                                        v_a_3509_ = crate::leanh::lean_ctor_get(v___x_3508_, 0);
                                        v_isSharedCheck_3653_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3508_)) as u8;
                                        if v_isSharedCheck_3653_ == 0 {
                                            v___x_3511_ = v___x_3508_;
                                            v_isShared_3512_ = v_isSharedCheck_3653_;
                                            state = 4;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3509_);
                                            crate::leanh::lean_dec(v___x_3508_);
                                            v___x_3511_ = crate::leanh::lean_box(0);
                                            v_isShared_3512_ = v_isSharedCheck_3653_;
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v___x_3506_, 1);
                                        crate::leanh::lean_dec(v_a_3504_);
                                        crate::leanh::lean_dec(v_a_3482_);
                                        crate::leanh::lean_dec_ref(v_p_3469_);
                                        v_a_3654_ = crate::leanh::lean_ctor_get(v___x_3508_, 0);
                                        v_isSharedCheck_3661_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3508_)) as u8;
                                        if v_isSharedCheck_3661_ == 0 {
                                            v___x_3656_ = v___x_3508_;
                                            v_isShared_3657_ = v_isSharedCheck_3661_;
                                            state = 33;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3654_);
                                            crate::leanh::lean_dec(v___x_3508_);
                                            v___x_3656_ = crate::leanh::lean_box(0);
                                            v_isShared_3657_ = v_isSharedCheck_3661_;
                                            state = 33;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_3502_);
                                    crate::leanh::lean_dec(v_val_3496_);
                                    crate::leanh::lean_dec(v_a_3482_);
                                    crate::leanh::lean_dec_ref(v_p_3469_);
                                    v_a_3662_ = crate::leanh::lean_ctor_get(v___x_3503_, 0);
                                    v_isSharedCheck_3669_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3503_)) as u8;
                                    if v_isSharedCheck_3669_ == 0 {
                                        v___x_3664_ = v___x_3503_;
                                        v_isShared_3665_ = v_isSharedCheck_3669_;
                                        state = 35;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3662_);
                                        crate::leanh::lean_dec(v___x_3503_);
                                        v___x_3664_ = crate::leanh::lean_box(0);
                                        v_isShared_3665_ = v_isSharedCheck_3669_;
                                        state = 35;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_3496_);
                                crate::leanh::lean_dec(v_a_3482_);
                                crate::leanh::lean_dec_ref(v_p_3469_);
                                v_a_3670_ = crate::leanh::lean_ctor_get(v___x_3501_, 0);
                                v_isSharedCheck_3677_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3501_)) as u8;
                                if v_isSharedCheck_3677_ == 0 {
                                    v___x_3672_ = v___x_3501_;
                                    v_isShared_3673_ = v_isSharedCheck_3677_;
                                    state = 37;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3670_);
                                    crate::leanh::lean_dec(v___x_3501_);
                                    v___x_3672_ = crate::leanh::lean_box(0);
                                    v_isShared_3673_ = v_isSharedCheck_3677_;
                                    state = 37;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_3496_);
                            crate::leanh::lean_dec(v_a_3482_);
                            crate::leanh::lean_dec_ref(v_p_3469_);
                            v_a_3678_ = crate::leanh::lean_ctor_get(v___x_3499_, 0);
                            v_isSharedCheck_3685_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3499_)) as u8;
                            if v_isSharedCheck_3685_ == 0 {
                                v___x_3680_ = v___x_3499_;
                                v_isShared_3681_ = v_isSharedCheck_3685_;
                                state = 39;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3678_);
                                crate::leanh::lean_dec(v___x_3499_);
                                v___x_3680_ = crate::leanh::lean_box(0);
                                v_isShared_3681_ = v_isSharedCheck_3685_;
                                state = 39;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_3496_);
                        crate::leanh::lean_dec(v_a_3482_);
                        crate::leanh::lean_dec_ref(v_p_3469_);
                        v_a_3686_ = crate::leanh::lean_ctor_get(v___x_3497_, 0);
                        v_isSharedCheck_3693_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3497_)) as u8;
                        if v_isSharedCheck_3693_ == 0 {
                            v___x_3688_ = v___x_3497_;
                            v_isShared_3689_ = v_isSharedCheck_3693_;
                            state = 41;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3686_);
                            crate::leanh::lean_dec(v___x_3497_);
                            v___x_3688_ = crate::leanh::lean_box(0);
                            v_isShared_3689_ = v_isSharedCheck_3693_;
                            state = 41;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3492_);
                    crate::leanh::lean_dec(v_a_3482_);
                    crate::leanh::lean_dec_ref(v_p_3469_);
                    v___x_3694_ = crate::leanh::lean_box(0);
                    if v_isShared_3495_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3494_, 0, v___x_3694_);
                        v___x_3696_ = v___x_3494_;
                        state = 43;
                        continue;
                    } else {
                        v_reuseFailAlloc_3697_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3694_);
                        v___x_3696_ = v_reuseFailAlloc_3697_;
                        state = 43;
                        continue;
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_3509_) == 1 {
                    crate::leanh::lean_del_object(v___x_3511_);
                    v_val_3513_ = crate::leanh::lean_ctor_get(v_a_3509_, 0);
                    crate::leanh::lean_inc_n(v_val_3513_, 2);
                    crate::leanh::lean_dec_ref_known(v_a_3509_, 1);
                    v___x_3514_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_val_3513_, v___x_3506_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_);
                    if crate::leanh::lean_obj_tag(v___x_3514_) == 0 {
                        v_a_3515_ = crate::leanh::lean_ctor_get(v___x_3514_, 0);
                        v_isSharedCheck_3640_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3514_)) as u8;
                        if v_isSharedCheck_3640_ == 0 {
                            v___x_3517_ = v___x_3514_;
                            v_isShared_3518_ = v_isSharedCheck_3640_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3515_);
                            crate::leanh::lean_dec(v___x_3514_);
                            v___x_3517_ = crate::leanh::lean_box(0);
                            v_isShared_3518_ = v_isSharedCheck_3640_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_3513_);
                        crate::leanh::lean_dec_ref_known(v___x_3506_, 1);
                        crate::leanh::lean_dec(v_a_3504_);
                        crate::leanh::lean_dec(v_a_3482_);
                        crate::leanh::lean_dec_ref(v_p_3469_);
                        v_a_3641_ = crate::leanh::lean_ctor_get(v___x_3514_, 0);
                        v_isSharedCheck_3648_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3514_)) as u8;
                        if v_isSharedCheck_3648_ == 0 {
                            v___x_3643_ = v___x_3514_;
                            v_isShared_3644_ = v_isSharedCheck_3648_;
                            state = 30;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3641_);
                            crate::leanh::lean_dec(v___x_3514_);
                            v___x_3643_ = crate::leanh::lean_box(0);
                            v_isShared_3644_ = v_isSharedCheck_3648_;
                            state = 30;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3509_);
                    crate::leanh::lean_dec_ref_known(v___x_3506_, 1);
                    crate::leanh::lean_dec(v_a_3504_);
                    crate::leanh::lean_dec(v_a_3482_);
                    crate::leanh::lean_dec_ref(v_p_3469_);
                    v___x_3649_ = crate::leanh::lean_box(0);
                    if v_isShared_3512_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3511_, 0, v___x_3649_);
                        v___x_3651_ = v___x_3511_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_3652_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3649_);
                        v___x_3651_ = v_reuseFailAlloc_3652_;
                        state = 32;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_3515_) == 1 {
                    crate::leanh::lean_del_object(v___x_3517_);
                    v_val_3519_ = crate::leanh::lean_ctor_get(v_a_3515_, 0);
                    v_isSharedCheck_3635_ = (!crate::leanh::lean_is_exclusive(v_a_3515_)) as u8;
                    if v_isSharedCheck_3635_ == 0 {
                        v___x_3521_ = v_a_3515_;
                        v_isShared_3522_ = v_isSharedCheck_3635_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3519_);
                        crate::leanh::lean_dec(v_a_3515_);
                        v___x_3521_ = crate::leanh::lean_box(0);
                        v_isShared_3522_ = v_isSharedCheck_3635_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3515_);
                    crate::leanh::lean_dec(v_val_3513_);
                    crate::leanh::lean_dec_ref_known(v___x_3506_, 1);
                    crate::leanh::lean_dec(v_a_3504_);
                    crate::leanh::lean_dec(v_a_3482_);
                    crate::leanh::lean_dec_ref(v_p_3469_);
                    v___x_3636_ = crate::leanh::lean_box(0);
                    if v_isShared_3518_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3517_, 0, v___x_3636_);
                        v___x_3638_ = v___x_3517_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_3639_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3636_);
                        v___x_3638_ = v_reuseFailAlloc_3639_;
                        state = 29;
                        continue;
                    }
                }
            }
            6 => {
                crate::leanh::lean_inc(v_val_3519_);
                v___x_3523_ = l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0(v_val_3519_, v___x_3506_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_);
                crate::leanh::lean_dec_ref_known(v___x_3506_, 1);
                if crate::leanh::lean_obj_tag(v___x_3523_) == 0 {
                    v_a_3524_ = crate::leanh::lean_ctor_get(v___x_3523_, 0);
                    crate::leanh::lean_inc(v_a_3524_);
                    crate::leanh::lean_dec_ref_known(v___x_3523_, 1);
                    v___x_3525_ = l_Lean_Meta_Grind_preprocessLight___redArg(
                        v_a_3524_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_,
                        v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3525_) == 0 {
                        v_a_3526_ = crate::leanh::lean_ctor_get(v___x_3525_, 0);
                        crate::leanh::lean_inc_n(v_a_3526_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_3525_, 1);
                        v___x_3527_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Int_Linear_Poly_normCommRing_x3f___closed__0),
                            core::ptr::addr_of_mut!(
                                l_Int_Linear_Poly_normCommRing_x3f___closed__0_once
                            ),
                            _init_l_Int_Linear_Poly_normCommRing_x3f___closed__0,
                        );
                        crate::leanh::lean_inc(v_a_3479_);
                        crate::leanh::lean_inc_ref(v_a_3478_);
                        crate::leanh::lean_inc(v_a_3477_);
                        crate::leanh::lean_inc_ref(v_a_3476_);
                        crate::leanh::lean_inc(v_a_3475_);
                        crate::leanh::lean_inc_ref(v_a_3474_);
                        crate::leanh::lean_inc(v_a_3473_);
                        crate::leanh::lean_inc_ref(v_a_3472_);
                        crate::leanh::lean_inc(v_a_3471_);
                        crate::leanh::lean_inc(v_a_3470_);
                        v___x_3528_ = lean_grind_internalize(
                            v_a_3526_,
                            v_a_3504_,
                            v___x_3527_,
                            v_a_3470_,
                            v_a_3471_,
                            v_a_3472_,
                            v_a_3473_,
                            v_a_3474_,
                            v_a_3475_,
                            v_a_3476_,
                            v_a_3477_,
                            v_a_3478_,
                            v_a_3479_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3528_) == 0 {
                            v_isSharedCheck_3609_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3528_)) as u8;
                            if v_isSharedCheck_3609_ == 0 {
                                v_unused_3610_ = crate::leanh::lean_ctor_get(v___x_3528_, 0);
                                crate::leanh::lean_dec(v_unused_3610_);
                                v___x_3530_ = v___x_3528_;
                                v_isShared_3531_ = v_isSharedCheck_3609_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3528_);
                                v___x_3530_ = crate::leanh::lean_box(0);
                                v_isShared_3531_ = v_isSharedCheck_3609_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3526_);
                            crate::leanh::lean_del_object(v___x_3521_);
                            crate::leanh::lean_dec(v_val_3519_);
                            crate::leanh::lean_dec(v_val_3513_);
                            crate::leanh::lean_dec(v_a_3482_);
                            crate::leanh::lean_dec_ref(v_p_3469_);
                            v_a_3611_ = crate::leanh::lean_ctor_get(v___x_3528_, 0);
                            v_isSharedCheck_3618_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3528_)) as u8;
                            if v_isSharedCheck_3618_ == 0 {
                                v___x_3613_ = v___x_3528_;
                                v_isShared_3614_ = v_isSharedCheck_3618_;
                                state = 23;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3611_);
                                crate::leanh::lean_dec(v___x_3528_);
                                v___x_3613_ = crate::leanh::lean_box(0);
                                v_isShared_3614_ = v_isSharedCheck_3618_;
                                state = 23;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3521_);
                        crate::leanh::lean_dec(v_val_3519_);
                        crate::leanh::lean_dec(v_val_3513_);
                        crate::leanh::lean_dec(v_a_3504_);
                        crate::leanh::lean_dec(v_a_3482_);
                        crate::leanh::lean_dec_ref(v_p_3469_);
                        v_a_3619_ = crate::leanh::lean_ctor_get(v___x_3525_, 0);
                        v_isSharedCheck_3626_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3525_)) as u8;
                        if v_isSharedCheck_3626_ == 0 {
                            v___x_3621_ = v___x_3525_;
                            v_isShared_3622_ = v_isSharedCheck_3626_;
                            state = 25;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3619_);
                            crate::leanh::lean_dec(v___x_3525_);
                            v___x_3621_ = crate::leanh::lean_box(0);
                            v_isShared_3622_ = v_isSharedCheck_3626_;
                            state = 25;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3521_);
                    crate::leanh::lean_dec(v_val_3519_);
                    crate::leanh::lean_dec(v_val_3513_);
                    crate::leanh::lean_dec(v_a_3504_);
                    crate::leanh::lean_dec(v_a_3482_);
                    crate::leanh::lean_dec_ref(v_p_3469_);
                    v_a_3627_ = crate::leanh::lean_ctor_get(v___x_3523_, 0);
                    v_isSharedCheck_3634_ = (!crate::leanh::lean_is_exclusive(v___x_3523_)) as u8;
                    if v_isSharedCheck_3634_ == 0 {
                        v___x_3629_ = v___x_3523_;
                        v_isShared_3630_ = v_isSharedCheck_3634_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3627_);
                        crate::leanh::lean_dec(v___x_3523_);
                        v___x_3629_ = crate::leanh::lean_box(0);
                        v_isShared_3630_ = v_isSharedCheck_3634_;
                        state = 27;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3532_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(
                    v_a_3526_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_,
                    v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_,
                );
                if crate::leanh::lean_obj_tag(v___x_3532_) == 0 {
                    v_a_3533_ = crate::leanh::lean_ctor_get(v___x_3532_, 0);
                    v_isSharedCheck_3600_ = (!crate::leanh::lean_is_exclusive(v___x_3532_)) as u8;
                    if v_isSharedCheck_3600_ == 0 {
                        v___x_3535_ = v___x_3532_;
                        v_isShared_3536_ = v_isSharedCheck_3600_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3533_);
                        crate::leanh::lean_dec(v___x_3532_);
                        v___x_3535_ = crate::leanh::lean_box(0);
                        v_isShared_3536_ = v_isSharedCheck_3600_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3530_);
                    crate::leanh::lean_del_object(v___x_3521_);
                    crate::leanh::lean_dec(v_val_3519_);
                    crate::leanh::lean_dec(v_val_3513_);
                    crate::leanh::lean_dec(v_a_3482_);
                    crate::leanh::lean_dec_ref(v_p_3469_);
                    v_a_3601_ = crate::leanh::lean_ctor_get(v___x_3532_, 0);
                    v_isSharedCheck_3608_ = (!crate::leanh::lean_is_exclusive(v___x_3532_)) as u8;
                    if v_isSharedCheck_3608_ == 0 {
                        v___x_3603_ = v___x_3532_;
                        v_isShared_3604_ = v_isSharedCheck_3608_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3601_);
                        crate::leanh::lean_dec(v___x_3532_);
                        v___x_3603_ = crate::leanh::lean_box(0);
                        v_isShared_3604_ = v_isSharedCheck_3608_;
                        state = 21;
                        continue;
                    }
                }
            }
            8 => {
                v___x_3546_ = l_Int_Linear_instBEqPoly_beq(v_p_3469_, v_a_3533_);
                if v___x_3546_ == 0 {
                    crate::leanh::lean_del_object(v___x_3530_);
                    v___f_3547_ = crate::leanh::lean_alloc_closure(
                        l_Int_Linear_Poly_normCommRing_x3f___lam__0___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_3547_, 0, v_a_3482_);
                    v___x_3548_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                    v___x_3549_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3548_, v___f_3547_, v_a_3470_);
                    if crate::leanh::lean_obj_tag(v___x_3549_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3549_, 1);
                        v_options_3550_ = crate::leanh::lean_ctor_get(v_a_3478_, 2);
                        v_hasTrace_3551_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_3550_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_3551_ == 0 {
                            crate::leanh::lean_dec_ref(v_p_3469_);
                            state = 9;
                            continue;
                        } else {
                            v_inheritedTraceOptions_3552_ =
                                crate::leanh::lean_ctor_get(v_a_3478_, 13);
                            v___x_3553_ = l_Int_Linear_Poly_normCommRing_x3f___closed__5;
                            v___x_3554_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Int_Linear_Poly_normCommRing_x3f___closed__8
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Int_Linear_Poly_normCommRing_x3f___closed__8_once
                                ),
                                _init_l_Int_Linear_Poly_normCommRing_x3f___closed__8,
                            );
                            v___x_3555_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_3552_,
                                v_options_3550_,
                                v___x_3554_,
                            );
                            if v___x_3555_ == 0 {
                                crate::leanh::lean_dec_ref(v_p_3469_);
                                state = 9;
                                continue;
                            } else {
                                v___x_3556_ =
                                    l_Int_Linear_Poly_pp___redArg(v_p_3469_, v_a_3470_, v_a_3478_);
                                if crate::leanh::lean_obj_tag(v___x_3556_) == 0 {
                                    v_a_3557_ = crate::leanh::lean_ctor_get(v___x_3556_, 0);
                                    crate::leanh::lean_inc(v_a_3557_);
                                    crate::leanh::lean_dec_ref_known(v___x_3556_, 1);
                                    crate::leanh::lean_inc(v_a_3533_);
                                    v___x_3558_ = l_Int_Linear_Poly_pp___redArg(
                                        v_a_3533_, v_a_3470_, v_a_3478_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_3558_) == 0 {
                                        v_a_3559_ = crate::leanh::lean_ctor_get(v___x_3558_, 0);
                                        crate::leanh::lean_inc(v_a_3559_);
                                        crate::leanh::lean_dec_ref_known(v___x_3558_, 1);
                                        v___x_3560_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Int_Linear_Poly_normCommRing_x3f___closed__10), core::ptr::addr_of_mut!(l_Int_Linear_Poly_normCommRing_x3f___closed__10_once), _init_l_Int_Linear_Poly_normCommRing_x3f___closed__10);
                                        v___x_3561_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_3561_, 0, v_a_3557_);
                                        crate::leanh::lean_ctor_set(v___x_3561_, 1, v___x_3560_);
                                        v___x_3562_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_3562_, 0, v___x_3561_);
                                        crate::leanh::lean_ctor_set(v___x_3562_, 1, v_a_3559_);
                                        v___x_3563_ = l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg(v___x_3553_, v___x_3562_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_);
                                        if crate::leanh::lean_obj_tag(v___x_3563_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_3563_, 1);
                                            state = 9;
                                            continue;
                                        } else {
                                            crate::leanh::lean_del_object(v___x_3535_);
                                            crate::leanh::lean_dec(v_a_3533_);
                                            crate::leanh::lean_del_object(v___x_3521_);
                                            crate::leanh::lean_dec(v_val_3519_);
                                            crate::leanh::lean_dec(v_val_3513_);
                                            v_a_3564_ = crate::leanh::lean_ctor_get(v___x_3563_, 0);
                                            v_isSharedCheck_3571_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_3563_))
                                                    as u8;
                                            if v_isSharedCheck_3571_ == 0 {
                                                v___x_3566_ = v___x_3563_;
                                                v_isShared_3567_ = v_isSharedCheck_3571_;
                                                state = 12;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_3564_);
                                                crate::leanh::lean_dec(v___x_3563_);
                                                v___x_3566_ = crate::leanh::lean_box(0);
                                                v_isShared_3567_ = v_isSharedCheck_3571_;
                                                state = 12;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_3557_);
                                        crate::leanh::lean_del_object(v___x_3535_);
                                        crate::leanh::lean_dec(v_a_3533_);
                                        crate::leanh::lean_del_object(v___x_3521_);
                                        crate::leanh::lean_dec(v_val_3519_);
                                        crate::leanh::lean_dec(v_val_3513_);
                                        v_a_3572_ = crate::leanh::lean_ctor_get(v___x_3558_, 0);
                                        v_isSharedCheck_3579_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3558_)) as u8;
                                        if v_isSharedCheck_3579_ == 0 {
                                            v___x_3574_ = v___x_3558_;
                                            v_isShared_3575_ = v_isSharedCheck_3579_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3572_);
                                            crate::leanh::lean_dec(v___x_3558_);
                                            v___x_3574_ = crate::leanh::lean_box(0);
                                            v_isShared_3575_ = v_isSharedCheck_3579_;
                                            state = 14;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_del_object(v___x_3535_);
                                    crate::leanh::lean_dec(v_a_3533_);
                                    crate::leanh::lean_del_object(v___x_3521_);
                                    crate::leanh::lean_dec(v_val_3519_);
                                    crate::leanh::lean_dec(v_val_3513_);
                                    v_a_3580_ = crate::leanh::lean_ctor_get(v___x_3556_, 0);
                                    v_isSharedCheck_3587_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3556_)) as u8;
                                    if v_isSharedCheck_3587_ == 0 {
                                        v___x_3582_ = v___x_3556_;
                                        v_isShared_3583_ = v_isSharedCheck_3587_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3580_);
                                        crate::leanh::lean_dec(v___x_3556_);
                                        v___x_3582_ = crate::leanh::lean_box(0);
                                        v_isShared_3583_ = v_isSharedCheck_3587_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3535_);
                        crate::leanh::lean_dec(v_a_3533_);
                        crate::leanh::lean_del_object(v___x_3521_);
                        crate::leanh::lean_dec(v_val_3519_);
                        crate::leanh::lean_dec(v_val_3513_);
                        crate::leanh::lean_dec_ref(v_p_3469_);
                        v_a_3588_ = crate::leanh::lean_ctor_get(v___x_3549_, 0);
                        v_isSharedCheck_3595_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3549_)) as u8;
                        if v_isSharedCheck_3595_ == 0 {
                            v___x_3590_ = v___x_3549_;
                            v_isShared_3591_ = v_isSharedCheck_3595_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3588_);
                            crate::leanh::lean_dec(v___x_3549_);
                            v___x_3590_ = crate::leanh::lean_box(0);
                            v_isShared_3591_ = v_isSharedCheck_3595_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3535_);
                    crate::leanh::lean_dec(v_a_3533_);
                    crate::leanh::lean_del_object(v___x_3521_);
                    crate::leanh::lean_dec(v_val_3519_);
                    crate::leanh::lean_dec(v_val_3513_);
                    crate::leanh::lean_dec(v_a_3482_);
                    crate::leanh::lean_dec_ref(v_p_3469_);
                    v___x_3596_ = crate::leanh::lean_box(0);
                    if v_isShared_3531_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3530_, 0, v___x_3596_);
                        v___x_3598_ = v___x_3530_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_3599_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3596_);
                        v___x_3598_ = v_reuseFailAlloc_3599_;
                        state = 20;
                        continue;
                    }
                }
            }
            9 => {
                v___x_3538_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3538_, 0, v_val_3519_);
                crate::leanh::lean_ctor_set(v___x_3538_, 1, v_a_3533_);
                v___x_3539_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3539_, 0, v_val_3513_);
                crate::leanh::lean_ctor_set(v___x_3539_, 1, v___x_3538_);
                if v_isShared_3522_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3521_, 0, v___x_3539_);
                    v___x_3541_ = v___x_3521_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3545_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3539_);
                    v___x_3541_ = v_reuseFailAlloc_3545_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_3536_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3535_, 0, v___x_3541_);
                    v___x_3543_ = v___x_3535_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3544_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3541_);
                    v___x_3543_ = v_reuseFailAlloc_3544_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3543_;
            }
            12 => {
                if v_isShared_3567_ == 0 {
                    v___x_3569_ = v___x_3566_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3570_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3564_);
                    v___x_3569_ = v_reuseFailAlloc_3570_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3569_;
            }
            14 => {
                if v_isShared_3575_ == 0 {
                    v___x_3577_ = v___x_3574_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3578_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3572_);
                    v___x_3577_ = v_reuseFailAlloc_3578_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3577_;
            }
            16 => {
                if v_isShared_3583_ == 0 {
                    v___x_3585_ = v___x_3582_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3586_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
                    v___x_3585_ = v_reuseFailAlloc_3586_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3585_;
            }
            18 => {
                if v_isShared_3591_ == 0 {
                    v___x_3593_ = v___x_3590_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3594_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
                    v___x_3593_ = v_reuseFailAlloc_3594_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3593_;
            }
            20 => {
                return v___x_3598_;
            }
            21 => {
                if v_isShared_3604_ == 0 {
                    v___x_3606_ = v___x_3603_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3607_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
                    v___x_3606_ = v_reuseFailAlloc_3607_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3606_;
            }
            23 => {
                if v_isShared_3614_ == 0 {
                    v___x_3616_ = v___x_3613_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3617_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
                    v___x_3616_ = v_reuseFailAlloc_3617_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3616_;
            }
            25 => {
                if v_isShared_3622_ == 0 {
                    v___x_3624_ = v___x_3621_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3625_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
                    v___x_3624_ = v_reuseFailAlloc_3625_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3624_;
            }
            27 => {
                if v_isShared_3630_ == 0 {
                    v___x_3632_ = v___x_3629_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3633_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
                    v___x_3632_ = v_reuseFailAlloc_3633_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3632_;
            }
            29 => {
                return v___x_3638_;
            }
            30 => {
                if v_isShared_3644_ == 0 {
                    v___x_3646_ = v___x_3643_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3647_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
                    v___x_3646_ = v_reuseFailAlloc_3647_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_3646_;
            }
            32 => {
                return v___x_3651_;
            }
            33 => {
                if v_isShared_3657_ == 0 {
                    v___x_3659_ = v___x_3656_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_3660_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
                    v___x_3659_ = v_reuseFailAlloc_3660_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_3659_;
            }
            35 => {
                if v_isShared_3665_ == 0 {
                    v___x_3667_ = v___x_3664_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3668_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3662_);
                    v___x_3667_ = v_reuseFailAlloc_3668_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_3667_;
            }
            37 => {
                if v_isShared_3673_ == 0 {
                    v___x_3675_ = v___x_3672_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3676_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
                    v___x_3675_ = v_reuseFailAlloc_3676_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3675_;
            }
            39 => {
                if v_isShared_3681_ == 0 {
                    v___x_3683_ = v___x_3680_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3684_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
                    v___x_3683_ = v_reuseFailAlloc_3684_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_3683_;
            }
            41 => {
                if v_isShared_3689_ == 0 {
                    v___x_3691_ = v___x_3688_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3692_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
                    v___x_3691_ = v_reuseFailAlloc_3692_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3691_;
            }
            43 => {
                return v___x_3696_;
            }
            44 => {
                if v_isShared_3702_ == 0 {
                    v___x_3704_ = v___x_3701_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_3705_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
                    v___x_3704_ = v_reuseFailAlloc_3705_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_3704_;
            }
            46 => {
                if v_isShared_3711_ == 0 {
                    v___x_3713_ = v___x_3710_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_3714_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
                    v___x_3713_ = v_reuseFailAlloc_3714_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_3713_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_normCommRing_x3f___boxed(
    mut v_p_3716_: *mut crate::leanh::LeanObject,
    mut v_a_3717_: *mut crate::leanh::LeanObject,
    mut v_a_3718_: *mut crate::leanh::LeanObject,
    mut v_a_3719_: *mut crate::leanh::LeanObject,
    mut v_a_3720_: *mut crate::leanh::LeanObject,
    mut v_a_3721_: *mut crate::leanh::LeanObject,
    mut v_a_3722_: *mut crate::leanh::LeanObject,
    mut v_a_3723_: *mut crate::leanh::LeanObject,
    mut v_a_3724_: *mut crate::leanh::LeanObject,
    mut v_a_3725_: *mut crate::leanh::LeanObject,
    mut v_a_3726_: *mut crate::leanh::LeanObject,
    mut v_a_3727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3728_ = l_Int_Linear_Poly_normCommRing_x3f(
        v_p_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_,
        v_a_3724_, v_a_3725_, v_a_3726_,
    );
    crate::leanh::lean_dec(v_a_3726_);
    crate::leanh::lean_dec_ref(v_a_3725_);
    crate::leanh::lean_dec(v_a_3724_);
    crate::leanh::lean_dec_ref(v_a_3723_);
    crate::leanh::lean_dec(v_a_3722_);
    crate::leanh::lean_dec_ref(v_a_3721_);
    crate::leanh::lean_dec(v_a_3720_);
    crate::leanh::lean_dec_ref(v_a_3719_);
    crate::leanh::lean_dec(v_a_3718_);
    crate::leanh::lean_dec(v_a_3717_);
    return v_res_3728_;
}
pub unsafe fn l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1(
    mut v_cls_3729_: *mut crate::leanh::LeanObject,
    mut v_msg_3730_: *mut crate::leanh::LeanObject,
    mut v___y_3731_: *mut crate::leanh::LeanObject,
    mut v___y_3732_: *mut crate::leanh::LeanObject,
    mut v___y_3733_: *mut crate::leanh::LeanObject,
    mut v___y_3734_: *mut crate::leanh::LeanObject,
    mut v___y_3735_: *mut crate::leanh::LeanObject,
    mut v___y_3736_: *mut crate::leanh::LeanObject,
    mut v___y_3737_: *mut crate::leanh::LeanObject,
    mut v___y_3738_: *mut crate::leanh::LeanObject,
    mut v___y_3739_: *mut crate::leanh::LeanObject,
    mut v___y_3740_: *mut crate::leanh::LeanObject,
    mut v___y_3741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3743_ = l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg(
        v_cls_3729_,
        v_msg_3730_,
        v___y_3738_,
        v___y_3739_,
        v___y_3740_,
        v___y_3741_,
    );
    return v___x_3743_;
}
pub unsafe fn l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___boxed(
    mut v_cls_3744_: *mut crate::leanh::LeanObject,
    mut v_msg_3745_: *mut crate::leanh::LeanObject,
    mut v___y_3746_: *mut crate::leanh::LeanObject,
    mut v___y_3747_: *mut crate::leanh::LeanObject,
    mut v___y_3748_: *mut crate::leanh::LeanObject,
    mut v___y_3749_: *mut crate::leanh::LeanObject,
    mut v___y_3750_: *mut crate::leanh::LeanObject,
    mut v___y_3751_: *mut crate::leanh::LeanObject,
    mut v___y_3752_: *mut crate::leanh::LeanObject,
    mut v___y_3753_: *mut crate::leanh::LeanObject,
    mut v___y_3754_: *mut crate::leanh::LeanObject,
    mut v___y_3755_: *mut crate::leanh::LeanObject,
    mut v___y_3756_: *mut crate::leanh::LeanObject,
    mut v___y_3757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3758_ = l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1(
        v_cls_3744_,
        v_msg_3745_,
        v___y_3746_,
        v___y_3747_,
        v___y_3748_,
        v___y_3749_,
        v___y_3750_,
        v___y_3751_,
        v___y_3752_,
        v___y_3753_,
        v___y_3754_,
        v___y_3755_,
        v___y_3756_,
    );
    crate::leanh::lean_dec(v___y_3756_);
    crate::leanh::lean_dec_ref(v___y_3755_);
    crate::leanh::lean_dec(v___y_3754_);
    crate::leanh::lean_dec_ref(v___y_3753_);
    crate::leanh::lean_dec(v___y_3752_);
    crate::leanh::lean_dec_ref(v___y_3751_);
    crate::leanh::lean_dec(v___y_3750_);
    crate::leanh::lean_dec_ref(v___y_3749_);
    crate::leanh::lean_dec(v___y_3748_);
    crate::leanh::lean_dec(v___y_3747_);
    crate::leanh::lean_dec_ref(v___y_3746_);
    return v_res_3758_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(
    mut v_00_u03b1_3759_: *mut crate::leanh::LeanObject,
    mut v_msg_3760_: *mut crate::leanh::LeanObject,
    mut v___y_3761_: *mut crate::leanh::LeanObject,
    mut v___y_3762_: *mut crate::leanh::LeanObject,
    mut v___y_3763_: *mut crate::leanh::LeanObject,
    mut v___y_3764_: *mut crate::leanh::LeanObject,
    mut v___y_3765_: *mut crate::leanh::LeanObject,
    mut v___y_3766_: *mut crate::leanh::LeanObject,
    mut v___y_3767_: *mut crate::leanh::LeanObject,
    mut v___y_3768_: *mut crate::leanh::LeanObject,
    mut v___y_3769_: *mut crate::leanh::LeanObject,
    mut v___y_3770_: *mut crate::leanh::LeanObject,
    mut v___y_3771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3773_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_3760_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
    return v___x_3773_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___boxed(
    mut v_00_u03b1_3774_: *mut crate::leanh::LeanObject,
    mut v_msg_3775_: *mut crate::leanh::LeanObject,
    mut v___y_3776_: *mut crate::leanh::LeanObject,
    mut v___y_3777_: *mut crate::leanh::LeanObject,
    mut v___y_3778_: *mut crate::leanh::LeanObject,
    mut v___y_3779_: *mut crate::leanh::LeanObject,
    mut v___y_3780_: *mut crate::leanh::LeanObject,
    mut v___y_3781_: *mut crate::leanh::LeanObject,
    mut v___y_3782_: *mut crate::leanh::LeanObject,
    mut v___y_3783_: *mut crate::leanh::LeanObject,
    mut v___y_3784_: *mut crate::leanh::LeanObject,
    mut v___y_3785_: *mut crate::leanh::LeanObject,
    mut v___y_3786_: *mut crate::leanh::LeanObject,
    mut v___y_3787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3788_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(v_00_u03b1_3774_, v_msg_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
    crate::leanh::lean_dec(v___y_3786_);
    crate::leanh::lean_dec_ref(v___y_3785_);
    crate::leanh::lean_dec(v___y_3784_);
    crate::leanh::lean_dec_ref(v___y_3783_);
    crate::leanh::lean_dec(v___y_3782_);
    crate::leanh::lean_dec_ref(v___y_3781_);
    crate::leanh::lean_dec(v___y_3780_);
    crate::leanh::lean_dec_ref(v___y_3779_);
    crate::leanh::lean_dec(v___y_3778_);
    crate::leanh::lean_dec(v___y_3777_);
    crate::leanh::lean_dec_ref(v___y_3776_);
    return v_res_3788_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
}
