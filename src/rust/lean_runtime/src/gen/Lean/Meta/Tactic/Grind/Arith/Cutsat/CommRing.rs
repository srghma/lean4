// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Tactic.Grind.Arith.CommRing.RingId Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.Tactic.Grind.Arith.Cutsat.Var Lean.Meta.Tactic.Grind.Arith.CommRing.Reify Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly
use crate::r#gen::Init::Data::Int::Linear::l_Int_Linear_instBEqPoly_beq;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4,
};
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
use crate::lean_imports_rs::Init::Prelude::{
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Types::lean_grind_internalize;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_float, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Int_Linear_Poly_isNonlinear___redArg___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Int_Linear_Poly_isNonlinear___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Int_Linear_Poly_isNonlinear___redArg___closed__1_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Int_Linear_Poly_isNonlinear___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__1_value)
        as *mut LeanObject;
static l_Int_Linear_Poly_isNonlinear___redArg___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__0_value)
                as *mut LeanObject,
            2929883540436775422 as *mut LeanObject,
        ],
    };
pub static l_Int_Linear_Poly_isNonlinear___redArg___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__1_value)
                as *mut LeanObject,
            1611444129324655608 as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_Poly_isNonlinear___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Int_Linear_Poly_isNonlinear___redArg___closed__3_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Int_Linear_Poly_isNonlinear___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Int_Linear_Poly_isNonlinear___redArg___closed__4_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Int_Linear_Poly_isNonlinear___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__4_value)
        as *mut LeanObject;
static l_Int_Linear_Poly_isNonlinear___redArg___closed__5_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__3_value)
                as *mut LeanObject,
            12847922472053947547 as *mut LeanObject,
        ],
    };
pub static l_Int_Linear_Poly_isNonlinear___redArg___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__4_value)
                as *mut LeanObject,
            10422657989269798688 as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_Poly_isNonlinear___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 105, 110, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [82, 105, 110, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 78, 101, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__2_value) as *mut LeanObject,10806710915646349764 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__3_value) as *mut LeanObject,10040236838748678500 as *mut LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value) as *mut LeanObject,9626815015619986526 as *mut LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__7_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__7_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__5_value) as *mut LeanObject,9626815015619986526 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__7_value) as *mut LeanObject,17185717442815859305 as *mut LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value) as *mut LeanObject,17636616155771105671 as *mut LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__0_value) as *mut LeanObject,17636616155771105671 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value) as *mut LeanObject,15578568367168711682 as *mut LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__3_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value) as *mut LeanObject,12050285396929189622 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__2_value) as *mut LeanObject,9341924117480681831 as *mut LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 72, 65, 100, 100, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__0_value) as *mut LeanObject,9594062259507646949 as *mut LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 65, 100, 100, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value) as *mut LeanObject,12050285396929189622 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__2_value) as *mut LeanObject,5442360487226035463 as *mut LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value) as *mut LeanObject,10393083817453678557 as *mut LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__4_value) as *mut LeanObject,10393083817453678557 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__6_value) as *mut LeanObject,10680564408669940870 as *mut LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 72, 77, 117, 108, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__0_value) as *mut LeanObject,18134279130838690737 as *mut LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 77, 117, 108, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value) as *mut LeanObject,12050285396929189622 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__2_value) as *mut LeanObject,7102027102192867304 as *mut LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__0_value) as *mut LeanObject,2929883540436775422 as *mut LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Int_Linear_Poly_isNonlinear___redArg___closed__3_value) as *mut LeanObject,12847922472053947547 as *mut LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 112, 111, 119, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__5_value) as *mut LeanObject,12050285396929189622 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__2_value) as *mut LeanObject,18388652353510661091 as *mut LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3_value) as *mut LeanObject;
static mut l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Int_Linear_Poly_normCommRing_x3f___closed__1_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__1_value) as *mut LeanObject;
pub static l_Int_Linear_Poly_normCommRing_x3f___closed__2_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__2_value) as *mut LeanObject;
pub static l_Int_Linear_Poly_normCommRing_x3f___closed__3_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__3_value) as *mut LeanObject;
pub static l_Int_Linear_Poly_normCommRing_x3f___closed__4_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__4_value) as *mut LeanObject;
static l_Int_Linear_Poly_normCommRing_x3f___closed__5_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__1_value)
                as *mut LeanObject,
            15947788021050471391 as *mut LeanObject,
        ],
    };
static l_Int_Linear_Poly_normCommRing_x3f___closed__5_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__2_value)
                as *mut LeanObject,
            11074150007773075224 as *mut LeanObject,
        ],
    };
static l_Int_Linear_Poly_normCommRing_x3f___closed__5_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__5_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__3_value)
                as *mut LeanObject,
            10199653630302390726 as *mut LeanObject,
        ],
    };
pub static l_Int_Linear_Poly_normCommRing_x3f___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__5_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__4_value)
                as *mut LeanObject,
            4162367480076971315 as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__5_value) as *mut LeanObject;
pub static l_Int_Linear_Poly_normCommRing_x3f___closed__6_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__6_value) as *mut LeanObject;
pub static l_Int_Linear_Poly_normCommRing_x3f___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__6_value)
                as *mut LeanObject,
            14231257465488249300 as *mut LeanObject,
        ],
    };
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__7_value) as *mut LeanObject;
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Int_Linear_Poly_normCommRing_x3f___closed__9_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_normCommRing_x3f___closed__9_value) as *mut LeanObject;
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_Linear_Poly_normCommRing_x3f___closed__10: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Int_Linear_Poly_isNonlinear___redArg(
    mut v_p_1905_: *mut LeanObject,
    mut v_a_1906_: *mut LeanObject,
    mut v_a_1907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1917_: u8 = 0;
    let mut v___y_1919_: u8 = 0;
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: u8 = 0;
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: u8 = 0;
    let mut v_isSharedCheck_1929_: u8 = 0;
    let mut v_a_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1933_: u8 = 0;
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1937_: u8 = 0;
    let mut v_a_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1941_: u8 = 0;
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1945_: u8 = 0;
    let mut v___x_1946_: u8 = 0;
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_1905_) == 1 {
                    v_v_1909_ = lean_ctor_get(v_p_1905_, 1);
                    v_p_1910_ = lean_ctor_get(v_p_1905_, 2);
                    v___x_1911_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(
                        v_v_1909_, v_a_1906_, v_a_1907_,
                    );
                    if lean_obj_tag(v___x_1911_) == 0 {
                        v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
                        lean_inc(v_a_1912_);
                        lean_dec_ref_known(v___x_1911_, 1);
                        v___x_1913_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(
                            v_v_1909_, v_a_1906_, v_a_1907_,
                        );
                        if lean_obj_tag(v___x_1913_) == 0 {
                            v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
                            v_isSharedCheck_1929_ = (!lean_is_exclusive(v___x_1913_)) as u8;
                            if v_isSharedCheck_1929_ == 0 {
                                v___x_1916_ = v___x_1913_;
                                v_isShared_1917_ = v_isSharedCheck_1929_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1914_);
                                lean_dec(v___x_1913_);
                                v___x_1916_ = lean_box(0);
                                v_isShared_1917_ = v_isSharedCheck_1929_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_1912_);
                            v_a_1930_ = lean_ctor_get(v___x_1913_, 0);
                            v_isSharedCheck_1937_ = (!lean_is_exclusive(v___x_1913_)) as u8;
                            if v_isSharedCheck_1937_ == 0 {
                                v___x_1932_ = v___x_1913_;
                                v_isShared_1933_ = v_isSharedCheck_1937_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_1930_);
                                lean_dec(v___x_1913_);
                                v___x_1932_ = lean_box(0);
                                v_isShared_1933_ = v_isSharedCheck_1937_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_a_1938_ = lean_ctor_get(v___x_1911_, 0);
                        v_isSharedCheck_1945_ = (!lean_is_exclusive(v___x_1911_)) as u8;
                        if v_isSharedCheck_1945_ == 0 {
                            v___x_1940_ = v___x_1911_;
                            v_isShared_1941_ = v_isSharedCheck_1945_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1938_);
                            lean_dec(v___x_1911_);
                            v___x_1940_ = lean_box(0);
                            v_isShared_1941_ = v_isSharedCheck_1945_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v___x_1946_ = 0;
                    v___x_1947_ = lean_box((v___x_1946_) as usize);
                    v___x_1948_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1948_, 0, v___x_1947_);
                    return v___x_1948_;
                }
            }
            1 => {
                v___x_1925_ = l_Int_Linear_Poly_isNonlinear___redArg___closed__2;
                v___x_1926_ = l_Lean_Expr_isAppOf(v_a_1912_, v___x_1925_);
                lean_dec(v_a_1912_);
                if v___x_1926_ == 0 {
                    v___x_1927_ = l_Int_Linear_Poly_isNonlinear___redArg___closed__5;
                    v___x_1928_ = l_Lean_Expr_isAppOf(v_a_1914_, v___x_1927_);
                    lean_dec(v_a_1914_);
                    v___y_1919_ = v___x_1928_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_a_1914_);
                    v___y_1919_ = v___x_1926_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_1919_ == 0 {
                    lean_del_object(v___x_1916_);
                    v_p_1905_ = v_p_1910_;
                    state = 0;
                    continue;
                } else {
                    v___x_1921_ = lean_box((v___y_1919_) as usize);
                    if v_isShared_1917_ == 0 {
                        lean_ctor_set(v___x_1916_, 0, v___x_1921_);
                        v___x_1923_ = v___x_1916_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
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
                    v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
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
                    v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
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
    mut v_p_1949_: *mut LeanObject,
    mut v_a_1950_: *mut LeanObject,
    mut v_a_1951_: *mut LeanObject,
    mut v_a_1952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1953_: *mut LeanObject = core::ptr::null_mut();
    v_res_1953_ = l_Int_Linear_Poly_isNonlinear___redArg(v_p_1949_, v_a_1950_, v_a_1951_);
    lean_dec_ref(v_a_1951_);
    lean_dec(v_a_1950_);
    lean_dec_ref(v_p_1949_);
    return v_res_1953_;
}
pub unsafe fn l_Int_Linear_Poly_isNonlinear(
    mut v_p_1954_: *mut LeanObject,
    mut v_a_1955_: *mut LeanObject,
    mut v_a_1956_: *mut LeanObject,
    mut v_a_1957_: *mut LeanObject,
    mut v_a_1958_: *mut LeanObject,
    mut v_a_1959_: *mut LeanObject,
    mut v_a_1960_: *mut LeanObject,
    mut v_a_1961_: *mut LeanObject,
    mut v_a_1962_: *mut LeanObject,
    mut v_a_1963_: *mut LeanObject,
    mut v_a_1964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    v___x_1966_ = l_Int_Linear_Poly_isNonlinear___redArg(v_p_1954_, v_a_1955_, v_a_1963_);
    return v___x_1966_;
}
pub unsafe fn l_Int_Linear_Poly_isNonlinear___boxed(
    mut v_p_1967_: *mut LeanObject,
    mut v_a_1968_: *mut LeanObject,
    mut v_a_1969_: *mut LeanObject,
    mut v_a_1970_: *mut LeanObject,
    mut v_a_1971_: *mut LeanObject,
    mut v_a_1972_: *mut LeanObject,
    mut v_a_1973_: *mut LeanObject,
    mut v_a_1974_: *mut LeanObject,
    mut v_a_1975_: *mut LeanObject,
    mut v_a_1976_: *mut LeanObject,
    mut v_a_1977_: *mut LeanObject,
    mut v_a_1978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1979_: *mut LeanObject = core::ptr::null_mut();
    v_res_1979_ = l_Int_Linear_Poly_isNonlinear(
        v_p_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_,
        v_a_1975_, v_a_1976_, v_a_1977_,
    );
    lean_dec(v_a_1977_);
    lean_dec_ref(v_a_1976_);
    lean_dec(v_a_1975_);
    lean_dec_ref(v_a_1974_);
    lean_dec(v_a_1973_);
    lean_dec_ref(v_a_1972_);
    lean_dec(v_a_1971_);
    lean_dec_ref(v_a_1970_);
    lean_dec(v_a_1969_);
    lean_dec(v_a_1968_);
    lean_dec_ref(v_p_1967_);
    return v_res_1979_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___redArg(
    mut v_a_1980_: *mut LeanObject,
    mut v_a_1981_: *mut LeanObject,
    mut v_a_1982_: *mut LeanObject,
    mut v_a_1983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1987_: u8 = 0;
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut v_unused_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: u8 = 0;
    let mut v_a_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2009_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1980_) == 0 {
                    v_isSharedCheck_1991_ = (!lean_is_exclusive(v_a_1980_)) as u8;
                    if v_isSharedCheck_1991_ == 0 {
                        v_unused_1992_ = lean_ctor_get(v_a_1980_, 0);
                        lean_dec(v_unused_1992_);
                        v___x_1986_ = v_a_1980_;
                        v_isShared_1987_ = v_isSharedCheck_1991_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_a_1980_);
                        v___x_1986_ = lean_box(0);
                        v_isShared_1987_ = v_isSharedCheck_1991_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_v_1993_ = lean_ctor_get(v_a_1980_, 1);
                    lean_inc(v_v_1993_);
                    v_p_1994_ = lean_ctor_get(v_a_1980_, 2);
                    lean_inc_ref(v_p_1994_);
                    lean_dec_ref_known(v_a_1980_, 3);
                    v___x_1995_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(
                        v_v_1993_, v_a_1982_, v_a_1983_,
                    );
                    lean_dec(v_v_1993_);
                    if lean_obj_tag(v___x_1995_) == 0 {
                        v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
                        lean_inc(v_a_1996_);
                        lean_dec_ref_known(v___x_1995_, 1);
                        v___x_1997_ =
                            l_Lean_Meta_Grind_getGeneration___redArg(v_a_1996_, v_a_1982_);
                        lean_dec(v_a_1996_);
                        if lean_obj_tag(v___x_1997_) == 0 {
                            v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
                            lean_inc(v_a_1998_);
                            lean_dec_ref_known(v___x_1997_, 1);
                            v___x_1999_ = lean_nat_dec_le(v_a_1998_, v_a_1981_);
                            if v___x_1999_ == 0 {
                                lean_dec(v_a_1981_);
                                v_a_1980_ = v_p_1994_;
                                v_a_1981_ = v_a_1998_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v_a_1998_);
                                v_a_1980_ = v_p_1994_;
                                state = 0;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_p_1994_);
                            lean_dec(v_a_1981_);
                            return v___x_1997_;
                        }
                    } else {
                        lean_dec_ref(v_p_1994_);
                        lean_dec(v_a_1981_);
                        v_a_2002_ = lean_ctor_get(v___x_1995_, 0);
                        v_isSharedCheck_2009_ = (!lean_is_exclusive(v___x_1995_)) as u8;
                        if v_isSharedCheck_2009_ == 0 {
                            v___x_2004_ = v___x_1995_;
                            v_isShared_2005_ = v_isSharedCheck_2009_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2002_);
                            lean_dec(v___x_1995_);
                            v___x_2004_ = lean_box(0);
                            v_isShared_2005_ = v_isSharedCheck_2009_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1987_ == 0 {
                    lean_ctor_set(v___x_1986_, 0, v_a_1981_);
                    v___x_1989_ = v___x_1986_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1981_);
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
                    v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
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
    mut v_a_2010_: *mut LeanObject,
    mut v_a_2011_: *mut LeanObject,
    mut v_a_2012_: *mut LeanObject,
    mut v_a_2013_: *mut LeanObject,
    mut v_a_2014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2015_: *mut LeanObject = core::ptr::null_mut();
    v_res_2015_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___redArg(v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
    lean_dec_ref(v_a_2013_);
    lean_dec(v_a_2012_);
    return v_res_2015_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go(
    mut v_a_2016_: *mut LeanObject,
    mut v_a_2017_: *mut LeanObject,
    mut v_a_2018_: *mut LeanObject,
    mut v_a_2019_: *mut LeanObject,
    mut v_a_2020_: *mut LeanObject,
    mut v_a_2021_: *mut LeanObject,
    mut v_a_2022_: *mut LeanObject,
    mut v_a_2023_: *mut LeanObject,
    mut v_a_2024_: *mut LeanObject,
    mut v_a_2025_: *mut LeanObject,
    mut v_a_2026_: *mut LeanObject,
    mut v_a_2027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    v___x_2029_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___redArg(v_a_2016_, v_a_2017_, v_a_2018_, v_a_2026_);
    return v___x_2029_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___boxed(
    mut v_a_2030_: *mut LeanObject,
    mut v_a_2031_: *mut LeanObject,
    mut v_a_2032_: *mut LeanObject,
    mut v_a_2033_: *mut LeanObject,
    mut v_a_2034_: *mut LeanObject,
    mut v_a_2035_: *mut LeanObject,
    mut v_a_2036_: *mut LeanObject,
    mut v_a_2037_: *mut LeanObject,
    mut v_a_2038_: *mut LeanObject,
    mut v_a_2039_: *mut LeanObject,
    mut v_a_2040_: *mut LeanObject,
    mut v_a_2041_: *mut LeanObject,
    mut v_a_2042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2043_: *mut LeanObject = core::ptr::null_mut();
    v_res_2043_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go(v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
    lean_dec(v_a_2041_);
    lean_dec_ref(v_a_2040_);
    lean_dec(v_a_2039_);
    lean_dec_ref(v_a_2038_);
    lean_dec(v_a_2037_);
    lean_dec_ref(v_a_2036_);
    lean_dec(v_a_2035_);
    lean_dec_ref(v_a_2034_);
    lean_dec(v_a_2033_);
    lean_dec(v_a_2032_);
    return v_res_2043_;
}
pub unsafe fn l_Int_Linear_Poly_getGeneration___redArg(
    mut v_p_2044_: *mut LeanObject,
    mut v_a_2045_: *mut LeanObject,
    mut v_a_2046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    v___x_2048_ = lean_unsigned_to_nat(0);
    v___x_2049_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing_0__Int_Linear_Poly_getGeneration_go___redArg(v_p_2044_, v___x_2048_, v_a_2045_, v_a_2046_);
    return v___x_2049_;
}
pub unsafe fn l_Int_Linear_Poly_getGeneration___redArg___boxed(
    mut v_p_2050_: *mut LeanObject,
    mut v_a_2051_: *mut LeanObject,
    mut v_a_2052_: *mut LeanObject,
    mut v_a_2053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2054_: *mut LeanObject = core::ptr::null_mut();
    v_res_2054_ = l_Int_Linear_Poly_getGeneration___redArg(v_p_2050_, v_a_2051_, v_a_2052_);
    lean_dec_ref(v_a_2052_);
    lean_dec(v_a_2051_);
    return v_res_2054_;
}
pub unsafe fn l_Int_Linear_Poly_getGeneration(
    mut v_p_2055_: *mut LeanObject,
    mut v_a_2056_: *mut LeanObject,
    mut v_a_2057_: *mut LeanObject,
    mut v_a_2058_: *mut LeanObject,
    mut v_a_2059_: *mut LeanObject,
    mut v_a_2060_: *mut LeanObject,
    mut v_a_2061_: *mut LeanObject,
    mut v_a_2062_: *mut LeanObject,
    mut v_a_2063_: *mut LeanObject,
    mut v_a_2064_: *mut LeanObject,
    mut v_a_2065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    v___x_2067_ = l_Int_Linear_Poly_getGeneration___redArg(v_p_2055_, v_a_2056_, v_a_2064_);
    return v___x_2067_;
}
pub unsafe fn l_Int_Linear_Poly_getGeneration___boxed(
    mut v_p_2068_: *mut LeanObject,
    mut v_a_2069_: *mut LeanObject,
    mut v_a_2070_: *mut LeanObject,
    mut v_a_2071_: *mut LeanObject,
    mut v_a_2072_: *mut LeanObject,
    mut v_a_2073_: *mut LeanObject,
    mut v_a_2074_: *mut LeanObject,
    mut v_a_2075_: *mut LeanObject,
    mut v_a_2076_: *mut LeanObject,
    mut v_a_2077_: *mut LeanObject,
    mut v_a_2078_: *mut LeanObject,
    mut v_a_2079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2080_: *mut LeanObject = core::ptr::null_mut();
    v_res_2080_ = l_Int_Linear_Poly_getGeneration(
        v_p_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_,
        v_a_2076_, v_a_2077_, v_a_2078_,
    );
    lean_dec(v_a_2078_);
    lean_dec_ref(v_a_2077_);
    lean_dec(v_a_2076_);
    lean_dec_ref(v_a_2075_);
    lean_dec(v_a_2074_);
    lean_dec_ref(v_a_2073_);
    lean_dec(v_a_2072_);
    lean_dec_ref(v_a_2071_);
    lean_dec(v_a_2070_);
    lean_dec(v_a_2069_);
    return v_res_2080_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(
    mut v_a_2081_: *mut LeanObject,
    mut v_a_2082_: *mut LeanObject,
    mut v_a_2083_: *mut LeanObject,
    mut v_a_2084_: *mut LeanObject,
    mut v_a_2085_: *mut LeanObject,
    mut v_a_2086_: *mut LeanObject,
    mut v_a_2087_: *mut LeanObject,
    mut v_a_2088_: *mut LeanObject,
    mut v_a_2089_: *mut LeanObject,
    mut v_a_2090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2098_: u8 = 0;
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2102_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2092_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2085_);
                if lean_obj_tag(v___x_2092_) == 0 {
                    v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
                    lean_inc(v_a_2093_);
                    lean_dec_ref_known(v___x_2092_, 1);
                    v___x_2094_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(
                        v_a_2093_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_,
                        v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_,
                    );
                    return v___x_2094_;
                } else {
                    v_a_2095_ = lean_ctor_get(v___x_2092_, 0);
                    v_isSharedCheck_2102_ = (!lean_is_exclusive(v___x_2092_)) as u8;
                    if v_isSharedCheck_2102_ == 0 {
                        v___x_2097_ = v___x_2092_;
                        v_isShared_2098_ = v_isSharedCheck_2102_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2095_);
                        lean_dec(v___x_2092_);
                        v___x_2097_ = lean_box(0);
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
                    v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
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
    mut v_a_2103_: *mut LeanObject,
    mut v_a_2104_: *mut LeanObject,
    mut v_a_2105_: *mut LeanObject,
    mut v_a_2106_: *mut LeanObject,
    mut v_a_2107_: *mut LeanObject,
    mut v_a_2108_: *mut LeanObject,
    mut v_a_2109_: *mut LeanObject,
    mut v_a_2110_: *mut LeanObject,
    mut v_a_2111_: *mut LeanObject,
    mut v_a_2112_: *mut LeanObject,
    mut v_a_2113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2114_: *mut LeanObject = core::ptr::null_mut();
    v_res_2114_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(
        v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_,
        v_a_2111_, v_a_2112_,
    );
    lean_dec(v_a_2112_);
    lean_dec_ref(v_a_2111_);
    lean_dec(v_a_2110_);
    lean_dec_ref(v_a_2109_);
    lean_dec(v_a_2108_);
    lean_dec_ref(v_a_2107_);
    lean_dec(v_a_2106_);
    lean_dec_ref(v_a_2105_);
    lean_dec(v_a_2104_);
    lean_dec(v_a_2103_);
    return v_res_2114_;
}
pub unsafe fn l_Int_Linear_Poly_normCommRing_x3f___lam__0(
    mut v_a_2115_: u8,
    mut v_s_2116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vars_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_x27_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_x27_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natDef_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dvds_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowers_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uppers_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_occurs_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextCnstrId_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_2132_: u8 = 0;
    let mut v_conflict_x3f_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_divMod_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntIds_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntInfos_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nonlinearOccs_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2143_: u8 = 0;
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2147_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_2117_ = lean_ctor_get(v_s_2116_, 0);
                v_varMap_2118_ = lean_ctor_get(v_s_2116_, 1);
                v_vars_x27_2119_ = lean_ctor_get(v_s_2116_, 2);
                v_varMap_x27_2120_ = lean_ctor_get(v_s_2116_, 3);
                v_natToIntMap_2121_ = lean_ctor_get(v_s_2116_, 4);
                v_natDef_2122_ = lean_ctor_get(v_s_2116_, 5);
                v_dvds_2123_ = lean_ctor_get(v_s_2116_, 6);
                v_lowers_2124_ = lean_ctor_get(v_s_2116_, 7);
                v_uppers_2125_ = lean_ctor_get(v_s_2116_, 8);
                v_diseqs_2126_ = lean_ctor_get(v_s_2116_, 9);
                v_elimEqs_2127_ = lean_ctor_get(v_s_2116_, 10);
                v_elimStack_2128_ = lean_ctor_get(v_s_2116_, 11);
                v_occurs_2129_ = lean_ctor_get(v_s_2116_, 12);
                v_assignment_2130_ = lean_ctor_get(v_s_2116_, 13);
                v_nextCnstrId_2131_ = lean_ctor_get(v_s_2116_, 14);
                v_caseSplits_2132_ = lean_ctor_get_uint8(
                    v_s_2116_,
                    (core::mem::size_of::<*mut LeanObject>() * 23) as u32,
                );
                v_conflict_x3f_2133_ = lean_ctor_get(v_s_2116_, 15);
                v_diseqSplits_2134_ = lean_ctor_get(v_s_2116_, 16);
                v_divMod_2135_ = lean_ctor_get(v_s_2116_, 17);
                v_toIntIds_2136_ = lean_ctor_get(v_s_2116_, 18);
                v_toIntInfos_2137_ = lean_ctor_get(v_s_2116_, 19);
                v_toIntTermMap_2138_ = lean_ctor_get(v_s_2116_, 20);
                v_toIntVarMap_2139_ = lean_ctor_get(v_s_2116_, 21);
                v_nonlinearOccs_2140_ = lean_ctor_get(v_s_2116_, 22);
                v_isSharedCheck_2147_ = (!lean_is_exclusive(v_s_2116_)) as u8;
                if v_isSharedCheck_2147_ == 0 {
                    v___x_2142_ = v_s_2116_;
                    v_isShared_2143_ = v_isSharedCheck_2147_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nonlinearOccs_2140_);
                    lean_inc(v_toIntVarMap_2139_);
                    lean_inc(v_toIntTermMap_2138_);
                    lean_inc(v_toIntInfos_2137_);
                    lean_inc(v_toIntIds_2136_);
                    lean_inc(v_divMod_2135_);
                    lean_inc(v_diseqSplits_2134_);
                    lean_inc(v_conflict_x3f_2133_);
                    lean_inc(v_nextCnstrId_2131_);
                    lean_inc(v_assignment_2130_);
                    lean_inc(v_occurs_2129_);
                    lean_inc(v_elimStack_2128_);
                    lean_inc(v_elimEqs_2127_);
                    lean_inc(v_diseqs_2126_);
                    lean_inc(v_uppers_2125_);
                    lean_inc(v_lowers_2124_);
                    lean_inc(v_dvds_2123_);
                    lean_inc(v_natDef_2122_);
                    lean_inc(v_natToIntMap_2121_);
                    lean_inc(v_varMap_x27_2120_);
                    lean_inc(v_vars_x27_2119_);
                    lean_inc(v_varMap_2118_);
                    lean_inc(v_vars_2117_);
                    lean_dec(v_s_2116_);
                    v___x_2142_ = lean_box(0);
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
                    v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 23, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_vars_2117_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_varMap_2118_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 2, v_vars_x27_2119_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 3, v_varMap_x27_2120_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 4, v_natToIntMap_2121_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 5, v_natDef_2122_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 6, v_dvds_2123_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 7, v_lowers_2124_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 8, v_uppers_2125_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 9, v_diseqs_2126_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 10, v_elimEqs_2127_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 11, v_elimStack_2128_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 12, v_occurs_2129_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 13, v_assignment_2130_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 14, v_nextCnstrId_2131_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 15, v_conflict_x3f_2133_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 16, v_diseqSplits_2134_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 17, v_divMod_2135_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 18, v_toIntIds_2136_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 19, v_toIntInfos_2137_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 20, v_toIntTermMap_2138_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 21, v_toIntVarMap_2139_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 22, v_nonlinearOccs_2140_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2146_,
                        (core::mem::size_of::<*mut LeanObject>() * 23) as u32,
                        v_caseSplits_2132_,
                    );
                    v___x_2145_ = v_reuseFailAlloc_2146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_2145_,
                    (core::mem::size_of::<*mut LeanObject>() * 23 + 1) as u32,
                    v_a_2115_,
                );
                return v___x_2145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_normCommRing_x3f___lam__0___boxed(
    mut v_a_2148_: *mut LeanObject,
    mut v_s_2149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_152961__boxed_2150_: u8 = 0;
    let mut v_res_2151_: *mut LeanObject = core::ptr::null_mut();
    v_a_152961__boxed_2150_ = (lean_unbox(v_a_2148_) as u8);
    v_res_2151_ = l_Int_Linear_Poly_normCommRing_x3f___lam__0(v_a_152961__boxed_2150_, v_s_2149_);
    return v_res_2151_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0(
    mut v_a_2152_: *mut LeanObject,
    mut v_s_2153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toRing_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextId_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_queue_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_basis_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recheck_2168_: u8 = 0;
    let mut v_invSet_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_2172_: u8 = 0;
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v_id_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denote_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2194_: u8 = 0;
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2202_: u8 = 0;
    let mut v_unused_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2204_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2154_ = lean_ctor_get(v_s_2153_, 0);
                v_invFn_x3f_2155_ = lean_ctor_get(v_s_2153_, 1);
                v_semiringId_x3f_2156_ = lean_ctor_get(v_s_2153_, 2);
                v_commSemiringInst_2157_ = lean_ctor_get(v_s_2153_, 3);
                v_commRingInst_2158_ = lean_ctor_get(v_s_2153_, 4);
                v_noZeroDivInst_x3f_2159_ = lean_ctor_get(v_s_2153_, 5);
                v_fieldInst_x3f_2160_ = lean_ctor_get(v_s_2153_, 6);
                v_powIdentityInst_x3f_2161_ = lean_ctor_get(v_s_2153_, 7);
                v_denoteEntries_2162_ = lean_ctor_get(v_s_2153_, 8);
                v_nextId_2163_ = lean_ctor_get(v_s_2153_, 9);
                v_steps_2164_ = lean_ctor_get(v_s_2153_, 10);
                v_queue_2165_ = lean_ctor_get(v_s_2153_, 11);
                v_basis_2166_ = lean_ctor_get(v_s_2153_, 12);
                v_diseqs_2167_ = lean_ctor_get(v_s_2153_, 13);
                v_recheck_2168_ = lean_ctor_get_uint8(
                    v_s_2153_,
                    (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                );
                v_invSet_2169_ = lean_ctor_get(v_s_2153_, 14);
                v_powIdentityVarCount_2170_ = lean_ctor_get(v_s_2153_, 15);
                v_numEq0_x3f_2171_ = lean_ctor_get(v_s_2153_, 16);
                v_numEq0Updated_2172_ = lean_ctor_get_uint8(
                    v_s_2153_,
                    (core::mem::size_of::<*mut LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_2204_ = (!lean_is_exclusive(v_s_2153_)) as u8;
                if v_isSharedCheck_2204_ == 0 {
                    v___x_2174_ = v_s_2153_;
                    v_isShared_2175_ = v_isSharedCheck_2204_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_numEq0_x3f_2171_);
                    lean_inc(v_powIdentityVarCount_2170_);
                    lean_inc(v_invSet_2169_);
                    lean_inc(v_diseqs_2167_);
                    lean_inc(v_basis_2166_);
                    lean_inc(v_queue_2165_);
                    lean_inc(v_steps_2164_);
                    lean_inc(v_nextId_2163_);
                    lean_inc(v_denoteEntries_2162_);
                    lean_inc(v_powIdentityInst_x3f_2161_);
                    lean_inc(v_fieldInst_x3f_2160_);
                    lean_inc(v_noZeroDivInst_x3f_2159_);
                    lean_inc(v_commRingInst_2158_);
                    lean_inc(v_commSemiringInst_2157_);
                    lean_inc(v_semiringId_x3f_2156_);
                    lean_inc(v_invFn_x3f_2155_);
                    lean_inc(v_toRing_2154_);
                    lean_dec(v_s_2153_);
                    v___x_2174_ = lean_box(0);
                    v_isShared_2175_ = v_isSharedCheck_2204_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_2176_ = lean_ctor_get(v_toRing_2154_, 0);
                v_type_2177_ = lean_ctor_get(v_toRing_2154_, 1);
                v_u_2178_ = lean_ctor_get(v_toRing_2154_, 2);
                v_ringInst_2179_ = lean_ctor_get(v_toRing_2154_, 3);
                v_semiringInst_2180_ = lean_ctor_get(v_toRing_2154_, 4);
                v_charInst_x3f_2181_ = lean_ctor_get(v_toRing_2154_, 5);
                v_addFn_x3f_2182_ = lean_ctor_get(v_toRing_2154_, 6);
                v_mulFn_x3f_2183_ = lean_ctor_get(v_toRing_2154_, 7);
                v_subFn_x3f_2184_ = lean_ctor_get(v_toRing_2154_, 8);
                v_powFn_x3f_2185_ = lean_ctor_get(v_toRing_2154_, 10);
                v_intCastFn_x3f_2186_ = lean_ctor_get(v_toRing_2154_, 11);
                v_natCastFn_x3f_2187_ = lean_ctor_get(v_toRing_2154_, 12);
                v_one_x3f_2188_ = lean_ctor_get(v_toRing_2154_, 13);
                v_vars_2189_ = lean_ctor_get(v_toRing_2154_, 14);
                v_varMap_2190_ = lean_ctor_get(v_toRing_2154_, 15);
                v_denote_2191_ = lean_ctor_get(v_toRing_2154_, 16);
                v_isSharedCheck_2202_ = (!lean_is_exclusive(v_toRing_2154_)) as u8;
                if v_isSharedCheck_2202_ == 0 {
                    v_unused_2203_ = lean_ctor_get(v_toRing_2154_, 9);
                    lean_dec(v_unused_2203_);
                    v___x_2193_ = v_toRing_2154_;
                    v_isShared_2194_ = v_isSharedCheck_2202_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_denote_2191_);
                    lean_inc(v_varMap_2190_);
                    lean_inc(v_vars_2189_);
                    lean_inc(v_one_x3f_2188_);
                    lean_inc(v_natCastFn_x3f_2187_);
                    lean_inc(v_intCastFn_x3f_2186_);
                    lean_inc(v_powFn_x3f_2185_);
                    lean_inc(v_subFn_x3f_2184_);
                    lean_inc(v_mulFn_x3f_2183_);
                    lean_inc(v_addFn_x3f_2182_);
                    lean_inc(v_charInst_x3f_2181_);
                    lean_inc(v_semiringInst_2180_);
                    lean_inc(v_ringInst_2179_);
                    lean_inc(v_u_2178_);
                    lean_inc(v_type_2177_);
                    lean_inc(v_id_2176_);
                    lean_dec(v_toRing_2154_);
                    v___x_2193_ = lean_box(0);
                    v_isShared_2194_ = v_isSharedCheck_2202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2195_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2195_, 0, v_a_2152_);
                if v_isShared_2194_ == 0 {
                    lean_ctor_set(v___x_2193_, 9, v___x_2195_);
                    v___x_2197_ = v___x_2193_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 17, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_id_2176_);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_type_2177_);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 2, v_u_2178_);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 3, v_ringInst_2179_);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 4, v_semiringInst_2180_);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 5, v_charInst_x3f_2181_);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 6, v_addFn_x3f_2182_);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 7, v_mulFn_x3f_2183_);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 8, v_subFn_x3f_2184_);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 9, v___x_2195_);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 10, v_powFn_x3f_2185_);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 11, v_intCastFn_x3f_2186_);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 12, v_natCastFn_x3f_2187_);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 13, v_one_x3f_2188_);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 14, v_vars_2189_);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 15, v_varMap_2190_);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 16, v_denote_2191_);
                    v___x_2197_ = v_reuseFailAlloc_2201_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2175_ == 0 {
                    lean_ctor_set(v___x_2174_, 0, v___x_2197_);
                    v___x_2199_ = v___x_2174_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 17, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_invFn_x3f_2155_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 2, v_semiringId_x3f_2156_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 3, v_commSemiringInst_2157_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 4, v_commRingInst_2158_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 5, v_noZeroDivInst_x3f_2159_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 6, v_fieldInst_x3f_2160_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 7, v_powIdentityInst_x3f_2161_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 8, v_denoteEntries_2162_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 9, v_nextId_2163_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 10, v_steps_2164_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 11, v_queue_2165_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 12, v_basis_2166_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 13, v_diseqs_2167_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 14, v_invSet_2169_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 15, v_powIdentityVarCount_2170_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 16, v_numEq0_x3f_2171_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2200_,
                        (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                        v_recheck_2168_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2200_,
                        (core::mem::size_of::<*mut LeanObject>() * 17 + 1) as u32,
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
    mut v_msgData_2205_: *mut LeanObject,
    mut v___y_2206_: *mut LeanObject,
    mut v___y_2207_: *mut LeanObject,
    mut v___y_2208_: *mut LeanObject,
    mut v___y_2209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    v___x_2211_ = lean_st_ref_get(v___y_2209_);
    v_env_2212_ = lean_ctor_get(v___x_2211_, 0);
    lean_inc_ref(v_env_2212_);
    lean_dec(v___x_2211_);
    v___x_2213_ = lean_st_ref_get(v___y_2207_);
    v_mctx_2214_ = lean_ctor_get(v___x_2213_, 0);
    lean_inc_ref(v_mctx_2214_);
    lean_dec(v___x_2213_);
    v_lctx_2215_ = lean_ctor_get(v___y_2206_, 2);
    v_options_2216_ = lean_ctor_get(v___y_2208_, 2);
    lean_inc_ref(v_options_2216_);
    lean_inc_ref(v_lctx_2215_);
    v___x_2217_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2217_, 0, v_env_2212_);
    lean_ctor_set(v___x_2217_, 1, v_mctx_2214_);
    lean_ctor_set(v___x_2217_, 2, v_lctx_2215_);
    lean_ctor_set(v___x_2217_, 3, v_options_2216_);
    v___x_2218_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2218_, 0, v___x_2217_);
    lean_ctor_set(v___x_2218_, 1, v_msgData_2205_);
    v___x_2219_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2219_, 0, v___x_2218_);
    return v___x_2219_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1_spec__4___boxed(
    mut v_msgData_2220_: *mut LeanObject,
    mut v___y_2221_: *mut LeanObject,
    mut v___y_2222_: *mut LeanObject,
    mut v___y_2223_: *mut LeanObject,
    mut v___y_2224_: *mut LeanObject,
    mut v___y_2225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2226_: *mut LeanObject = core::ptr::null_mut();
    v_res_2226_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msgData_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
    lean_dec(v___y_2224_);
    lean_dec_ref(v___y_2223_);
    lean_dec(v___y_2222_);
    lean_dec_ref(v___y_2221_);
    return v_res_2226_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(
    mut v_msg_2227_: *mut LeanObject,
    mut v___y_2228_: *mut LeanObject,
    mut v___y_2229_: *mut LeanObject,
    mut v___y_2230_: *mut LeanObject,
    mut v___y_2231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2238_: u8 = 0;
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2243_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2233_ = lean_ctor_get(v___y_2230_, 5);
                v___x_2234_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
                v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
                v_isSharedCheck_2243_ = (!lean_is_exclusive(v___x_2234_)) as u8;
                if v_isSharedCheck_2243_ == 0 {
                    v___x_2237_ = v___x_2234_;
                    v_isShared_2238_ = v_isSharedCheck_2243_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2235_);
                    lean_dec(v___x_2234_);
                    v___x_2237_ = lean_box(0);
                    v_isShared_2238_ = v_isSharedCheck_2243_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2233_);
                v___x_2239_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2239_, 0, v_ref_2233_);
                lean_ctor_set(v___x_2239_, 1, v_a_2235_);
                if v_isShared_2238_ == 0 {
                    lean_ctor_set_tag(v___x_2237_, 1);
                    lean_ctor_set(v___x_2237_, 0, v___x_2239_);
                    v___x_2241_ = v___x_2237_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2239_);
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
    mut v_msg_2244_: *mut LeanObject,
    mut v___y_2245_: *mut LeanObject,
    mut v___y_2246_: *mut LeanObject,
    mut v___y_2247_: *mut LeanObject,
    mut v___y_2248_: *mut LeanObject,
    mut v___y_2249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2250_: *mut LeanObject = core::ptr::null_mut();
    v_res_2250_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
    lean_dec(v___y_2248_);
    lean_dec_ref(v___y_2247_);
    lean_dec(v___y_2246_);
    lean_dec_ref(v___y_2245_);
    return v_res_2250_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1()
-> *mut LeanObject {
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    v___x_2252_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__0;
    v___x_2253_ = l_Lean_stringToMessageData(v___x_2252_);
    return v___x_2253_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(
    mut v_type_2254_: *mut LeanObject,
    mut v___y_2255_: *mut LeanObject,
    mut v___y_2256_: *mut LeanObject,
    mut v___y_2257_: *mut LeanObject,
    mut v___y_2258_: *mut LeanObject,
    mut v___y_2259_: *mut LeanObject,
    mut v___y_2260_: *mut LeanObject,
    mut v___y_2261_: *mut LeanObject,
    mut v___y_2262_: *mut LeanObject,
    mut v___y_2263_: *mut LeanObject,
    mut v___y_2264_: *mut LeanObject,
    mut v___y_2265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2271_: u8 = 0;
    let mut v_val_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2280_: u8 = 0;
    let mut v_a_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2284_: u8 = 0;
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_type_2254_);
                v___x_2267_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v_type_2254_,
                    v___y_2262_,
                    v___y_2263_,
                    v___y_2264_,
                    v___y_2265_,
                );
                if lean_obj_tag(v___x_2267_) == 0 {
                    v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
                    v_isSharedCheck_2280_ = (!lean_is_exclusive(v___x_2267_)) as u8;
                    if v_isSharedCheck_2280_ == 0 {
                        v___x_2270_ = v___x_2267_;
                        v_isShared_2271_ = v_isSharedCheck_2280_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2268_);
                        lean_dec(v___x_2267_);
                        v___x_2270_ = lean_box(0);
                        v_isShared_2271_ = v_isSharedCheck_2280_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_type_2254_);
                    v_a_2281_ = lean_ctor_get(v___x_2267_, 0);
                    v_isSharedCheck_2288_ = (!lean_is_exclusive(v___x_2267_)) as u8;
                    if v_isSharedCheck_2288_ == 0 {
                        v___x_2283_ = v___x_2267_;
                        v_isShared_2284_ = v_isSharedCheck_2288_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2281_);
                        lean_dec(v___x_2267_);
                        v___x_2283_ = lean_box(0);
                        v_isShared_2284_ = v_isSharedCheck_2288_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2268_) == 1 {
                    lean_dec_ref(v_type_2254_);
                    v_val_2272_ = lean_ctor_get(v_a_2268_, 0);
                    lean_inc(v_val_2272_);
                    lean_dec_ref_known(v_a_2268_, 1);
                    if v_isShared_2271_ == 0 {
                        lean_ctor_set(v___x_2270_, 0, v_val_2272_);
                        v___x_2274_ = v___x_2270_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_val_2272_);
                        v___x_2274_ = v_reuseFailAlloc_2275_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2270_);
                    lean_dec(v_a_2268_);
                    v___x_2276_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1_once), _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7___closed__1);
                    v___x_2277_ = l_Lean_indentExpr(v_type_2254_);
                    v___x_2278_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2278_, 0, v___x_2276_);
                    lean_ctor_set(v___x_2278_, 1, v___x_2277_);
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
                    v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
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
    mut v_type_2289_: *mut LeanObject,
    mut v___y_2290_: *mut LeanObject,
    mut v___y_2291_: *mut LeanObject,
    mut v___y_2292_: *mut LeanObject,
    mut v___y_2293_: *mut LeanObject,
    mut v___y_2294_: *mut LeanObject,
    mut v___y_2295_: *mut LeanObject,
    mut v___y_2296_: *mut LeanObject,
    mut v___y_2297_: *mut LeanObject,
    mut v___y_2298_: *mut LeanObject,
    mut v___y_2299_: *mut LeanObject,
    mut v___y_2300_: *mut LeanObject,
    mut v___y_2301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2302_: *mut LeanObject = core::ptr::null_mut();
    v_res_2302_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v_type_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
    lean_dec(v___y_2300_);
    lean_dec_ref(v___y_2299_);
    lean_dec(v___y_2298_);
    lean_dec_ref(v___y_2297_);
    lean_dec(v___y_2296_);
    lean_dec_ref(v___y_2295_);
    lean_dec(v___y_2294_);
    lean_dec_ref(v___y_2293_);
    lean_dec(v___y_2292_);
    lean_dec(v___y_2291_);
    lean_dec_ref(v___y_2290_);
    return v_res_2302_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(
    mut v_type_2303_: *mut LeanObject,
    mut v_u_2304_: *mut LeanObject,
    mut v_instDeclName_2305_: *mut LeanObject,
    mut v_declName_2306_: *mut LeanObject,
    mut v_expectedInst_2307_: *mut LeanObject,
    mut v___y_2308_: *mut LeanObject,
    mut v___y_2309_: *mut LeanObject,
    mut v___y_2310_: *mut LeanObject,
    mut v___y_2311_: *mut LeanObject,
    mut v___y_2312_: *mut LeanObject,
    mut v___y_2313_: *mut LeanObject,
    mut v___y_2314_: *mut LeanObject,
    mut v___y_2315_: *mut LeanObject,
    mut v___y_2316_: *mut LeanObject,
    mut v___y_2317_: *mut LeanObject,
    mut v___y_2318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2335_: u8 = 0;
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2339_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2320_ = lean_box(0);
                v___x_2321_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2321_, 0, v_u_2304_);
                lean_ctor_set(v___x_2321_, 1, v___x_2320_);
                lean_inc_ref(v___x_2321_);
                v___x_2322_ = l_Lean_mkConst(v_instDeclName_2305_, v___x_2321_);
                lean_inc_ref(v_type_2303_);
                v___x_2323_ = l_Lean_Expr_app___override(v___x_2322_, v_type_2303_);
                v___x_2324_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_2323_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
                if lean_obj_tag(v___x_2324_) == 0 {
                    v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
                    lean_inc_n(v_a_2325_, 2);
                    lean_dec_ref_known(v___x_2324_, 1);
                    lean_inc(v_declName_2306_);
                    v___x_2326_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
                        v_declName_2306_,
                        v_a_2325_,
                        v_expectedInst_2307_,
                        v___y_2315_,
                        v___y_2316_,
                        v___y_2317_,
                        v___y_2318_,
                    );
                    if lean_obj_tag(v___x_2326_) == 0 {
                        lean_dec_ref_known(v___x_2326_, 1);
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
                        if lean_obj_tag(v___x_2329_) == 0 {
                            v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
                            lean_inc(v_a_2330_);
                            lean_dec_ref_known(v___x_2329_, 1);
                            v___x_2331_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_2330_, v___y_2314_);
                            return v___x_2331_;
                        } else {
                            return v___x_2329_;
                        }
                    } else {
                        lean_dec(v_a_2325_);
                        lean_dec_ref_known(v___x_2321_, 2);
                        lean_dec(v_declName_2306_);
                        lean_dec_ref(v_type_2303_);
                        v_a_2332_ = lean_ctor_get(v___x_2326_, 0);
                        v_isSharedCheck_2339_ = (!lean_is_exclusive(v___x_2326_)) as u8;
                        if v_isSharedCheck_2339_ == 0 {
                            v___x_2334_ = v___x_2326_;
                            v_isShared_2335_ = v_isSharedCheck_2339_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2332_);
                            lean_dec(v___x_2326_);
                            v___x_2334_ = lean_box(0);
                            v_isShared_2335_ = v_isSharedCheck_2339_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_2321_, 2);
                    lean_dec_ref(v_expectedInst_2307_);
                    lean_dec(v_declName_2306_);
                    lean_dec_ref(v_type_2303_);
                    return v___x_2324_;
                }
            }
            1 => {
                if v_isShared_2335_ == 0 {
                    v___x_2337_ = v___x_2334_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_type_2340_: *mut LeanObject = *_args.add(0);
    let mut v_u_2341_: *mut LeanObject = *_args.add(1);
    let mut v_instDeclName_2342_: *mut LeanObject = *_args.add(2);
    let mut v_declName_2343_: *mut LeanObject = *_args.add(3);
    let mut v_expectedInst_2344_: *mut LeanObject = *_args.add(4);
    let mut v___y_2345_: *mut LeanObject = *_args.add(5);
    let mut v___y_2346_: *mut LeanObject = *_args.add(6);
    let mut v___y_2347_: *mut LeanObject = *_args.add(7);
    let mut v___y_2348_: *mut LeanObject = *_args.add(8);
    let mut v___y_2349_: *mut LeanObject = *_args.add(9);
    let mut v___y_2350_: *mut LeanObject = *_args.add(10);
    let mut v___y_2351_: *mut LeanObject = *_args.add(11);
    let mut v___y_2352_: *mut LeanObject = *_args.add(12);
    let mut v___y_2353_: *mut LeanObject = *_args.add(13);
    let mut v___y_2354_: *mut LeanObject = *_args.add(14);
    let mut v___y_2355_: *mut LeanObject = *_args.add(15);
    let mut v___y_2356_: *mut LeanObject = *_args.add(16);
    let mut v_res_2357_: *mut LeanObject = core::ptr::null_mut();
    v_res_2357_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_2340_, v_u_2341_, v_instDeclName_2342_, v_declName_2343_, v_expectedInst_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
    lean_dec(v___y_2355_);
    lean_dec_ref(v___y_2354_);
    lean_dec(v___y_2353_);
    lean_dec_ref(v___y_2352_);
    lean_dec(v___y_2351_);
    lean_dec_ref(v___y_2350_);
    lean_dec(v___y_2349_);
    lean_dec_ref(v___y_2348_);
    lean_dec(v___y_2347_);
    lean_dec(v___y_2346_);
    lean_dec_ref(v___y_2345_);
    return v_res_2357_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(
    mut v___y_2374_: *mut LeanObject,
    mut v___y_2375_: *mut LeanObject,
    mut v___y_2376_: *mut LeanObject,
    mut v___y_2377_: *mut LeanObject,
    mut v___y_2378_: *mut LeanObject,
    mut v___y_2379_: *mut LeanObject,
    mut v___y_2380_: *mut LeanObject,
    mut v___y_2381_: *mut LeanObject,
    mut v___y_2382_: *mut LeanObject,
    mut v___y_2383_: *mut LeanObject,
    mut v___y_2384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2390_: u8 = 0;
    let mut v_toRing_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expectedInst_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2413_: u8 = 0;
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2417_: u8 = 0;
    let mut v_unused_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2422_: u8 = 0;
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2426_: u8 = 0;
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut v_a_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2431_: u8 = 0;
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2434_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2386_) == 0 {
                    v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
                    v_isSharedCheck_2427_ = (!lean_is_exclusive(v___x_2386_)) as u8;
                    if v_isSharedCheck_2427_ == 0 {
                        v___x_2389_ = v___x_2386_;
                        v_isShared_2390_ = v_isSharedCheck_2427_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2387_);
                        lean_dec(v___x_2386_);
                        v___x_2389_ = lean_box(0);
                        v_isShared_2390_ = v_isSharedCheck_2427_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2428_ = lean_ctor_get(v___x_2386_, 0);
                    v_isSharedCheck_2435_ = (!lean_is_exclusive(v___x_2386_)) as u8;
                    if v_isSharedCheck_2435_ == 0 {
                        v___x_2430_ = v___x_2386_;
                        v_isShared_2431_ = v_isSharedCheck_2435_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2428_);
                        lean_dec(v___x_2386_);
                        v___x_2430_ = lean_box(0);
                        v_isShared_2431_ = v_isSharedCheck_2435_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_2391_ = lean_ctor_get(v_a_2387_, 0);
                lean_inc_ref(v_toRing_2391_);
                lean_dec(v_a_2387_);
                v_negFn_x3f_2392_ = lean_ctor_get(v_toRing_2391_, 9);
                if lean_obj_tag(v_negFn_x3f_2392_) == 1 {
                    lean_inc_ref(v_negFn_x3f_2392_);
                    lean_dec_ref(v_toRing_2391_);
                    v_val_2393_ = lean_ctor_get(v_negFn_x3f_2392_, 0);
                    lean_inc(v_val_2393_);
                    lean_dec_ref_known(v_negFn_x3f_2392_, 1);
                    if v_isShared_2390_ == 0 {
                        lean_ctor_set(v___x_2389_, 0, v_val_2393_);
                        v___x_2395_ = v___x_2389_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_val_2393_);
                        v___x_2395_ = v_reuseFailAlloc_2396_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2389_);
                    v_type_2397_ = lean_ctor_get(v_toRing_2391_, 1);
                    lean_inc_ref_n(v_type_2397_, 2);
                    v_u_2398_ = lean_ctor_get(v_toRing_2391_, 2);
                    lean_inc_n(v_u_2398_, 2);
                    v_ringInst_2399_ = lean_ctor_get(v_toRing_2391_, 3);
                    lean_inc_ref(v_ringInst_2399_);
                    lean_dec_ref(v_toRing_2391_);
                    v___x_2400_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__4;
                    v___x_2401_ = lean_box(0);
                    v___x_2402_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2402_, 0, v_u_2398_);
                    lean_ctor_set(v___x_2402_, 1, v___x_2401_);
                    v___x_2403_ = l_Lean_mkConst(v___x_2400_, v___x_2402_);
                    v_expectedInst_2404_ =
                        l_Lean_mkAppB(v___x_2403_, v_type_2397_, v_ringInst_2399_);
                    v___x_2405_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__6;
                    v___x_2406_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___closed__8;
                    v___x_2407_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4(v_type_2397_, v_u_2398_, v___x_2405_, v___x_2406_, v_expectedInst_2404_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
                    if lean_obj_tag(v___x_2407_) == 0 {
                        v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
                        lean_inc_n(v_a_2408_, 2);
                        lean_dec_ref_known(v___x_2407_, 1);
                        v___f_2409_ = lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1___lam__0 as *mut core::ffi::c_void, 2, 1);
                        lean_closure_set(v___f_2409_, 0, v_a_2408_);
                        v___x_2410_ =
                            l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
                                v___f_2409_,
                                v___y_2374_,
                                v___y_2375_,
                            );
                        if lean_obj_tag(v___x_2410_) == 0 {
                            v_isSharedCheck_2417_ = (!lean_is_exclusive(v___x_2410_)) as u8;
                            if v_isSharedCheck_2417_ == 0 {
                                v_unused_2418_ = lean_ctor_get(v___x_2410_, 0);
                                lean_dec(v_unused_2418_);
                                v___x_2412_ = v___x_2410_;
                                v_isShared_2413_ = v_isSharedCheck_2417_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_2410_);
                                v___x_2412_ = lean_box(0);
                                v_isShared_2413_ = v_isSharedCheck_2417_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2408_);
                            v_a_2419_ = lean_ctor_get(v___x_2410_, 0);
                            v_isSharedCheck_2426_ = (!lean_is_exclusive(v___x_2410_)) as u8;
                            if v_isSharedCheck_2426_ == 0 {
                                v___x_2421_ = v___x_2410_;
                                v_isShared_2422_ = v_isSharedCheck_2426_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_2419_);
                                lean_dec(v___x_2410_);
                                v___x_2421_ = lean_box(0);
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
                    lean_ctor_set(v___x_2412_, 0, v_a_2408_);
                    v___x_2415_ = v___x_2412_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2408_);
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
                    v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
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
                    v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
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
    mut v___y_2436_: *mut LeanObject,
    mut v___y_2437_: *mut LeanObject,
    mut v___y_2438_: *mut LeanObject,
    mut v___y_2439_: *mut LeanObject,
    mut v___y_2440_: *mut LeanObject,
    mut v___y_2441_: *mut LeanObject,
    mut v___y_2442_: *mut LeanObject,
    mut v___y_2443_: *mut LeanObject,
    mut v___y_2444_: *mut LeanObject,
    mut v___y_2445_: *mut LeanObject,
    mut v___y_2446_: *mut LeanObject,
    mut v___y_2447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2448_: *mut LeanObject = core::ptr::null_mut();
    v_res_2448_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
    lean_dec(v___y_2446_);
    lean_dec_ref(v___y_2445_);
    lean_dec(v___y_2444_);
    lean_dec_ref(v___y_2443_);
    lean_dec(v___y_2442_);
    lean_dec_ref(v___y_2441_);
    lean_dec(v___y_2440_);
    lean_dec_ref(v___y_2439_);
    lean_dec(v___y_2438_);
    lean_dec(v___y_2437_);
    lean_dec_ref(v___y_2436_);
    return v_res_2448_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    v___x_2456_ = lean_unsigned_to_nat(0);
    v___x_2457_ = lean_nat_to_int(v___x_2456_);
    return v___x_2457_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(
    mut v_k_2464_: *mut LeanObject,
    mut v___y_2465_: *mut LeanObject,
    mut v___y_2466_: *mut LeanObject,
    mut v___y_2467_: *mut LeanObject,
    mut v___y_2468_: *mut LeanObject,
    mut v___y_2469_: *mut LeanObject,
    mut v___y_2470_: *mut LeanObject,
    mut v___y_2471_: *mut LeanObject,
    mut v___y_2472_: *mut LeanObject,
    mut v___y_2473_: *mut LeanObject,
    mut v___y_2474_: *mut LeanObject,
    mut v___y_2475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toRing_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2495_: u8 = 0;
    let mut v_ofNatInst_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: u8 = 0;
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2521_: u8 = 0;
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2526_: u8 = 0;
    let mut v_val_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2531_: u8 = 0;
    let mut v_a_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2535_: u8 = 0;
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2539_: u8 = 0;
    let mut v_a_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2543_: u8 = 0;
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2546_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2477_) == 0 {
                    v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
                    lean_inc(v_a_2478_);
                    lean_dec_ref_known(v___x_2477_, 1);
                    v_toRing_2479_ = lean_ctor_get(v_a_2478_, 0);
                    lean_inc_ref(v_toRing_2479_);
                    lean_dec(v_a_2478_);
                    v_type_2480_ = lean_ctor_get(v_toRing_2479_, 1);
                    lean_inc_ref_n(v_type_2480_, 2);
                    v_u_2481_ = lean_ctor_get(v_toRing_2479_, 2);
                    lean_inc(v_u_2481_);
                    v_semiringInst_2482_ = lean_ctor_get(v_toRing_2479_, 4);
                    lean_inc_ref(v_semiringInst_2482_);
                    lean_dec_ref(v_toRing_2479_);
                    v___x_2483_ = lean_nat_abs(v_k_2464_);
                    v_n_2484_ = l_Lean_mkRawNatLit(v___x_2483_);
                    v___x_2485_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__1;
                    v___x_2486_ = lean_box(0);
                    v___x_2487_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2487_, 0, v_u_2481_);
                    lean_ctor_set(v___x_2487_, 1, v___x_2486_);
                    lean_inc_ref(v___x_2487_);
                    v___x_2488_ = l_Lean_mkConst(v___x_2485_, v___x_2487_);
                    lean_inc_ref(v_n_2484_);
                    v___x_2489_ = l_Lean_mkAppB(v___x_2488_, v_type_2480_, v_n_2484_);
                    v___x_2490_ = lean_box(0);
                    v___x_2491_ = l_Lean_Meta_synthInstance_x3f(
                        v___x_2489_,
                        v___x_2490_,
                        v___y_2472_,
                        v___y_2473_,
                        v___y_2474_,
                        v___y_2475_,
                    );
                    if lean_obj_tag(v___x_2491_) == 0 {
                        v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
                        v_isSharedCheck_2531_ = (!lean_is_exclusive(v___x_2491_)) as u8;
                        if v_isSharedCheck_2531_ == 0 {
                            v___x_2494_ = v___x_2491_;
                            v_isShared_2495_ = v_isSharedCheck_2531_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2492_);
                            lean_dec(v___x_2491_);
                            v___x_2494_ = lean_box(0);
                            v_isShared_2495_ = v_isSharedCheck_2531_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_2487_, 2);
                        lean_dec_ref(v_n_2484_);
                        lean_dec_ref(v_semiringInst_2482_);
                        lean_dec_ref(v_type_2480_);
                        v_a_2532_ = lean_ctor_get(v___x_2491_, 0);
                        v_isSharedCheck_2539_ = (!lean_is_exclusive(v___x_2491_)) as u8;
                        if v_isSharedCheck_2539_ == 0 {
                            v___x_2534_ = v___x_2491_;
                            v_isShared_2535_ = v_isSharedCheck_2539_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2532_);
                            lean_dec(v___x_2491_);
                            v___x_2534_ = lean_box(0);
                            v_isShared_2535_ = v_isSharedCheck_2539_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v_a_2540_ = lean_ctor_get(v___x_2477_, 0);
                    v_isSharedCheck_2547_ = (!lean_is_exclusive(v___x_2477_)) as u8;
                    if v_isSharedCheck_2547_ == 0 {
                        v___x_2542_ = v___x_2477_;
                        v_isShared_2543_ = v_isSharedCheck_2547_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2540_);
                        lean_dec(v___x_2477_);
                        v___x_2542_ = lean_box(0);
                        v_isShared_2543_ = v_isSharedCheck_2547_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2492_) == 1 {
                    lean_dec_ref(v_semiringInst_2482_);
                    v_val_2527_ = lean_ctor_get(v_a_2492_, 0);
                    lean_inc(v_val_2527_);
                    lean_dec_ref_known(v_a_2492_, 1);
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
                    lean_dec(v_a_2492_);
                    v___x_2528_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__6;
                    lean_inc_ref(v___x_2487_);
                    v___x_2529_ = l_Lean_mkConst(v___x_2528_, v___x_2487_);
                    lean_inc_ref(v_n_2484_);
                    lean_inc_ref(v_type_2480_);
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
                v___x_2512_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once), _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
                v___x_2513_ = lean_int_dec_lt(v_k_2464_, v___x_2512_);
                if v___x_2513_ == 0 {
                    if v_isShared_2495_ == 0 {
                        lean_ctor_set(v___x_2494_, 0, v_n_2511_);
                        v___x_2515_ = v___x_2494_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_n_2511_);
                        v___x_2515_ = v_reuseFailAlloc_2516_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2494_);
                    v___x_2517_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1(v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
                    if lean_obj_tag(v___x_2517_) == 0 {
                        v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
                        v_isSharedCheck_2526_ = (!lean_is_exclusive(v___x_2517_)) as u8;
                        if v_isSharedCheck_2526_ == 0 {
                            v___x_2520_ = v___x_2517_;
                            v_isShared_2521_ = v_isSharedCheck_2526_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2518_);
                            lean_dec(v___x_2517_);
                            v___x_2520_ = lean_box(0);
                            v_isShared_2521_ = v_isSharedCheck_2526_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_n_2511_);
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
                    lean_ctor_set(v___x_2520_, 0, v___x_2522_);
                    v___x_2524_ = v___x_2520_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
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
                    v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
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
                    v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
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
    mut v_k_2548_: *mut LeanObject,
    mut v___y_2549_: *mut LeanObject,
    mut v___y_2550_: *mut LeanObject,
    mut v___y_2551_: *mut LeanObject,
    mut v___y_2552_: *mut LeanObject,
    mut v___y_2553_: *mut LeanObject,
    mut v___y_2554_: *mut LeanObject,
    mut v___y_2555_: *mut LeanObject,
    mut v___y_2556_: *mut LeanObject,
    mut v___y_2557_: *mut LeanObject,
    mut v___y_2558_: *mut LeanObject,
    mut v___y_2559_: *mut LeanObject,
    mut v___y_2560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2561_: *mut LeanObject = core::ptr::null_mut();
    v_res_2561_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
    lean_dec(v___y_2559_);
    lean_dec_ref(v___y_2558_);
    lean_dec(v___y_2557_);
    lean_dec_ref(v___y_2556_);
    lean_dec(v___y_2555_);
    lean_dec_ref(v___y_2554_);
    lean_dec(v___y_2553_);
    lean_dec_ref(v___y_2552_);
    lean_dec(v___y_2551_);
    lean_dec(v___y_2550_);
    lean_dec_ref(v___y_2549_);
    lean_dec(v_k_2548_);
    return v_res_2561_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0(
    mut v_a_2562_: *mut LeanObject,
    mut v_s_2563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toRing_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextId_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_queue_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_basis_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recheck_2578_: u8 = 0;
    let mut v_invSet_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_2582_: u8 = 0;
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2585_: u8 = 0;
    let mut v_id_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denote_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2604_: u8 = 0;
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2612_: u8 = 0;
    let mut v_unused_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2564_ = lean_ctor_get(v_s_2563_, 0);
                v_invFn_x3f_2565_ = lean_ctor_get(v_s_2563_, 1);
                v_semiringId_x3f_2566_ = lean_ctor_get(v_s_2563_, 2);
                v_commSemiringInst_2567_ = lean_ctor_get(v_s_2563_, 3);
                v_commRingInst_2568_ = lean_ctor_get(v_s_2563_, 4);
                v_noZeroDivInst_x3f_2569_ = lean_ctor_get(v_s_2563_, 5);
                v_fieldInst_x3f_2570_ = lean_ctor_get(v_s_2563_, 6);
                v_powIdentityInst_x3f_2571_ = lean_ctor_get(v_s_2563_, 7);
                v_denoteEntries_2572_ = lean_ctor_get(v_s_2563_, 8);
                v_nextId_2573_ = lean_ctor_get(v_s_2563_, 9);
                v_steps_2574_ = lean_ctor_get(v_s_2563_, 10);
                v_queue_2575_ = lean_ctor_get(v_s_2563_, 11);
                v_basis_2576_ = lean_ctor_get(v_s_2563_, 12);
                v_diseqs_2577_ = lean_ctor_get(v_s_2563_, 13);
                v_recheck_2578_ = lean_ctor_get_uint8(
                    v_s_2563_,
                    (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                );
                v_invSet_2579_ = lean_ctor_get(v_s_2563_, 14);
                v_powIdentityVarCount_2580_ = lean_ctor_get(v_s_2563_, 15);
                v_numEq0_x3f_2581_ = lean_ctor_get(v_s_2563_, 16);
                v_numEq0Updated_2582_ = lean_ctor_get_uint8(
                    v_s_2563_,
                    (core::mem::size_of::<*mut LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_2614_ = (!lean_is_exclusive(v_s_2563_)) as u8;
                if v_isSharedCheck_2614_ == 0 {
                    v___x_2584_ = v_s_2563_;
                    v_isShared_2585_ = v_isSharedCheck_2614_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_numEq0_x3f_2581_);
                    lean_inc(v_powIdentityVarCount_2580_);
                    lean_inc(v_invSet_2579_);
                    lean_inc(v_diseqs_2577_);
                    lean_inc(v_basis_2576_);
                    lean_inc(v_queue_2575_);
                    lean_inc(v_steps_2574_);
                    lean_inc(v_nextId_2573_);
                    lean_inc(v_denoteEntries_2572_);
                    lean_inc(v_powIdentityInst_x3f_2571_);
                    lean_inc(v_fieldInst_x3f_2570_);
                    lean_inc(v_noZeroDivInst_x3f_2569_);
                    lean_inc(v_commRingInst_2568_);
                    lean_inc(v_commSemiringInst_2567_);
                    lean_inc(v_semiringId_x3f_2566_);
                    lean_inc(v_invFn_x3f_2565_);
                    lean_inc(v_toRing_2564_);
                    lean_dec(v_s_2563_);
                    v___x_2584_ = lean_box(0);
                    v_isShared_2585_ = v_isSharedCheck_2614_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_2586_ = lean_ctor_get(v_toRing_2564_, 0);
                v_type_2587_ = lean_ctor_get(v_toRing_2564_, 1);
                v_u_2588_ = lean_ctor_get(v_toRing_2564_, 2);
                v_ringInst_2589_ = lean_ctor_get(v_toRing_2564_, 3);
                v_semiringInst_2590_ = lean_ctor_get(v_toRing_2564_, 4);
                v_charInst_x3f_2591_ = lean_ctor_get(v_toRing_2564_, 5);
                v_mulFn_x3f_2592_ = lean_ctor_get(v_toRing_2564_, 7);
                v_subFn_x3f_2593_ = lean_ctor_get(v_toRing_2564_, 8);
                v_negFn_x3f_2594_ = lean_ctor_get(v_toRing_2564_, 9);
                v_powFn_x3f_2595_ = lean_ctor_get(v_toRing_2564_, 10);
                v_intCastFn_x3f_2596_ = lean_ctor_get(v_toRing_2564_, 11);
                v_natCastFn_x3f_2597_ = lean_ctor_get(v_toRing_2564_, 12);
                v_one_x3f_2598_ = lean_ctor_get(v_toRing_2564_, 13);
                v_vars_2599_ = lean_ctor_get(v_toRing_2564_, 14);
                v_varMap_2600_ = lean_ctor_get(v_toRing_2564_, 15);
                v_denote_2601_ = lean_ctor_get(v_toRing_2564_, 16);
                v_isSharedCheck_2612_ = (!lean_is_exclusive(v_toRing_2564_)) as u8;
                if v_isSharedCheck_2612_ == 0 {
                    v_unused_2613_ = lean_ctor_get(v_toRing_2564_, 6);
                    lean_dec(v_unused_2613_);
                    v___x_2603_ = v_toRing_2564_;
                    v_isShared_2604_ = v_isSharedCheck_2612_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_denote_2601_);
                    lean_inc(v_varMap_2600_);
                    lean_inc(v_vars_2599_);
                    lean_inc(v_one_x3f_2598_);
                    lean_inc(v_natCastFn_x3f_2597_);
                    lean_inc(v_intCastFn_x3f_2596_);
                    lean_inc(v_powFn_x3f_2595_);
                    lean_inc(v_negFn_x3f_2594_);
                    lean_inc(v_subFn_x3f_2593_);
                    lean_inc(v_mulFn_x3f_2592_);
                    lean_inc(v_charInst_x3f_2591_);
                    lean_inc(v_semiringInst_2590_);
                    lean_inc(v_ringInst_2589_);
                    lean_inc(v_u_2588_);
                    lean_inc(v_type_2587_);
                    lean_inc(v_id_2586_);
                    lean_dec(v_toRing_2564_);
                    v___x_2603_ = lean_box(0);
                    v_isShared_2604_ = v_isSharedCheck_2612_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2605_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2605_, 0, v_a_2562_);
                if v_isShared_2604_ == 0 {
                    lean_ctor_set(v___x_2603_, 6, v___x_2605_);
                    v___x_2607_ = v___x_2603_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 17, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_id_2586_);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_type_2587_);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 2, v_u_2588_);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 3, v_ringInst_2589_);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 4, v_semiringInst_2590_);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 5, v_charInst_x3f_2591_);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 6, v___x_2605_);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 7, v_mulFn_x3f_2592_);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 8, v_subFn_x3f_2593_);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 9, v_negFn_x3f_2594_);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 10, v_powFn_x3f_2595_);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 11, v_intCastFn_x3f_2596_);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 12, v_natCastFn_x3f_2597_);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 13, v_one_x3f_2598_);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 14, v_vars_2599_);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 15, v_varMap_2600_);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 16, v_denote_2601_);
                    v___x_2607_ = v_reuseFailAlloc_2611_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2585_ == 0 {
                    lean_ctor_set(v___x_2584_, 0, v___x_2607_);
                    v___x_2609_ = v___x_2584_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 17, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2607_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_invFn_x3f_2565_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 2, v_semiringId_x3f_2566_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 3, v_commSemiringInst_2567_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 4, v_commRingInst_2568_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 5, v_noZeroDivInst_x3f_2569_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 6, v_fieldInst_x3f_2570_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 7, v_powIdentityInst_x3f_2571_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 8, v_denoteEntries_2572_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 9, v_nextId_2573_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 10, v_steps_2574_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 11, v_queue_2575_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 12, v_basis_2576_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 13, v_diseqs_2577_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 14, v_invSet_2579_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 15, v_powIdentityVarCount_2580_);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 16, v_numEq0_x3f_2581_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2610_,
                        (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                        v_recheck_2578_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2610_,
                        (core::mem::size_of::<*mut LeanObject>() * 17 + 1) as u32,
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
    mut v_type_2615_: *mut LeanObject,
    mut v_u_2616_: *mut LeanObject,
    mut v_instDeclName_2617_: *mut LeanObject,
    mut v_declName_2618_: *mut LeanObject,
    mut v_expectedInst_2619_: *mut LeanObject,
    mut v___y_2620_: *mut LeanObject,
    mut v___y_2621_: *mut LeanObject,
    mut v___y_2622_: *mut LeanObject,
    mut v___y_2623_: *mut LeanObject,
    mut v___y_2624_: *mut LeanObject,
    mut v___y_2625_: *mut LeanObject,
    mut v___y_2626_: *mut LeanObject,
    mut v___y_2627_: *mut LeanObject,
    mut v___y_2628_: *mut LeanObject,
    mut v___y_2629_: *mut LeanObject,
    mut v___y_2630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2649_: u8 = 0;
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2632_ = lean_box(0);
                lean_inc_n(v_u_2616_, 2);
                v___x_2633_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2633_, 0, v_u_2616_);
                lean_ctor_set(v___x_2633_, 1, v___x_2632_);
                v___x_2634_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2634_, 0, v_u_2616_);
                lean_ctor_set(v___x_2634_, 1, v___x_2633_);
                v___x_2635_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2635_, 0, v_u_2616_);
                lean_ctor_set(v___x_2635_, 1, v___x_2634_);
                lean_inc_ref(v___x_2635_);
                v___x_2636_ = l_Lean_mkConst(v_instDeclName_2617_, v___x_2635_);
                lean_inc_ref_n(v_type_2615_, 3);
                v___x_2637_ = l_Lean_mkApp3(v___x_2636_, v_type_2615_, v_type_2615_, v_type_2615_);
                v___x_2638_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_2637_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
                if lean_obj_tag(v___x_2638_) == 0 {
                    v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
                    lean_inc_n(v_a_2639_, 2);
                    lean_dec_ref_known(v___x_2638_, 1);
                    lean_inc(v_declName_2618_);
                    v___x_2640_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
                        v_declName_2618_,
                        v_a_2639_,
                        v_expectedInst_2619_,
                        v___y_2627_,
                        v___y_2628_,
                        v___y_2629_,
                        v___y_2630_,
                    );
                    if lean_obj_tag(v___x_2640_) == 0 {
                        lean_dec_ref_known(v___x_2640_, 1);
                        v___x_2641_ = l_Lean_mkConst(v_declName_2618_, v___x_2635_);
                        lean_inc_ref_n(v_type_2615_, 2);
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
                        if lean_obj_tag(v___x_2643_) == 0 {
                            v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
                            lean_inc(v_a_2644_);
                            lean_dec_ref_known(v___x_2643_, 1);
                            v___x_2645_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_2644_, v___y_2626_);
                            return v___x_2645_;
                        } else {
                            return v___x_2643_;
                        }
                    } else {
                        lean_dec(v_a_2639_);
                        lean_dec_ref_known(v___x_2635_, 2);
                        lean_dec(v_declName_2618_);
                        lean_dec_ref(v_type_2615_);
                        v_a_2646_ = lean_ctor_get(v___x_2640_, 0);
                        v_isSharedCheck_2653_ = (!lean_is_exclusive(v___x_2640_)) as u8;
                        if v_isSharedCheck_2653_ == 0 {
                            v___x_2648_ = v___x_2640_;
                            v_isShared_2649_ = v_isSharedCheck_2653_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2646_);
                            lean_dec(v___x_2640_);
                            v___x_2648_ = lean_box(0);
                            v_isShared_2649_ = v_isSharedCheck_2653_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_2635_, 2);
                    lean_dec_ref(v_expectedInst_2619_);
                    lean_dec(v_declName_2618_);
                    lean_dec_ref(v_type_2615_);
                    return v___x_2638_;
                }
            }
            1 => {
                if v_isShared_2649_ == 0 {
                    v___x_2651_ = v___x_2648_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_type_2654_: *mut LeanObject = *_args.add(0);
    let mut v_u_2655_: *mut LeanObject = *_args.add(1);
    let mut v_instDeclName_2656_: *mut LeanObject = *_args.add(2);
    let mut v_declName_2657_: *mut LeanObject = *_args.add(3);
    let mut v_expectedInst_2658_: *mut LeanObject = *_args.add(4);
    let mut v___y_2659_: *mut LeanObject = *_args.add(5);
    let mut v___y_2660_: *mut LeanObject = *_args.add(6);
    let mut v___y_2661_: *mut LeanObject = *_args.add(7);
    let mut v___y_2662_: *mut LeanObject = *_args.add(8);
    let mut v___y_2663_: *mut LeanObject = *_args.add(9);
    let mut v___y_2664_: *mut LeanObject = *_args.add(10);
    let mut v___y_2665_: *mut LeanObject = *_args.add(11);
    let mut v___y_2666_: *mut LeanObject = *_args.add(12);
    let mut v___y_2667_: *mut LeanObject = *_args.add(13);
    let mut v___y_2668_: *mut LeanObject = *_args.add(14);
    let mut v___y_2669_: *mut LeanObject = *_args.add(15);
    let mut v___y_2670_: *mut LeanObject = *_args.add(16);
    let mut v_res_2671_: *mut LeanObject = core::ptr::null_mut();
    v_res_2671_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_2654_, v_u_2655_, v_instDeclName_2656_, v_declName_2657_, v_expectedInst_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
    lean_dec(v___y_2669_);
    lean_dec_ref(v___y_2668_);
    lean_dec(v___y_2667_);
    lean_dec_ref(v___y_2666_);
    lean_dec(v___y_2665_);
    lean_dec_ref(v___y_2664_);
    lean_dec(v___y_2663_);
    lean_dec_ref(v___y_2662_);
    lean_dec(v___y_2661_);
    lean_dec(v___y_2660_);
    lean_dec_ref(v___y_2659_);
    return v_res_2671_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(
    mut v___y_2688_: *mut LeanObject,
    mut v___y_2689_: *mut LeanObject,
    mut v___y_2690_: *mut LeanObject,
    mut v___y_2691_: *mut LeanObject,
    mut v___y_2692_: *mut LeanObject,
    mut v___y_2693_: *mut LeanObject,
    mut v___y_2694_: *mut LeanObject,
    mut v___y_2695_: *mut LeanObject,
    mut v___y_2696_: *mut LeanObject,
    mut v___y_2697_: *mut LeanObject,
    mut v___y_2698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2704_: u8 = 0;
    let mut v_toRing_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expectedInst_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2730_: u8 = 0;
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2734_: u8 = 0;
    let mut v_unused_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2739_: u8 = 0;
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2743_: u8 = 0;
    let mut v_isSharedCheck_2744_: u8 = 0;
    let mut v_a_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2748_: u8 = 0;
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2751_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2700_) == 0 {
                    v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
                    v_isSharedCheck_2744_ = (!lean_is_exclusive(v___x_2700_)) as u8;
                    if v_isSharedCheck_2744_ == 0 {
                        v___x_2703_ = v___x_2700_;
                        v_isShared_2704_ = v_isSharedCheck_2744_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2701_);
                        lean_dec(v___x_2700_);
                        v___x_2703_ = lean_box(0);
                        v_isShared_2704_ = v_isSharedCheck_2744_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2745_ = lean_ctor_get(v___x_2700_, 0);
                    v_isSharedCheck_2752_ = (!lean_is_exclusive(v___x_2700_)) as u8;
                    if v_isSharedCheck_2752_ == 0 {
                        v___x_2747_ = v___x_2700_;
                        v_isShared_2748_ = v_isSharedCheck_2752_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2745_);
                        lean_dec(v___x_2700_);
                        v___x_2747_ = lean_box(0);
                        v_isShared_2748_ = v_isSharedCheck_2752_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_2705_ = lean_ctor_get(v_a_2701_, 0);
                lean_inc_ref(v_toRing_2705_);
                lean_dec(v_a_2701_);
                v_addFn_x3f_2706_ = lean_ctor_get(v_toRing_2705_, 6);
                if lean_obj_tag(v_addFn_x3f_2706_) == 1 {
                    lean_inc_ref(v_addFn_x3f_2706_);
                    lean_dec_ref(v_toRing_2705_);
                    v_val_2707_ = lean_ctor_get(v_addFn_x3f_2706_, 0);
                    lean_inc(v_val_2707_);
                    lean_dec_ref_known(v_addFn_x3f_2706_, 1);
                    if v_isShared_2704_ == 0 {
                        lean_ctor_set(v___x_2703_, 0, v_val_2707_);
                        v___x_2709_ = v___x_2703_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_val_2707_);
                        v___x_2709_ = v_reuseFailAlloc_2710_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2703_);
                    v_type_2711_ = lean_ctor_get(v_toRing_2705_, 1);
                    lean_inc_ref_n(v_type_2711_, 3);
                    v_u_2712_ = lean_ctor_get(v_toRing_2705_, 2);
                    lean_inc_n(v_u_2712_, 2);
                    v_semiringInst_2713_ = lean_ctor_get(v_toRing_2705_, 4);
                    lean_inc_ref(v_semiringInst_2713_);
                    lean_dec_ref(v_toRing_2705_);
                    v___x_2714_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__1;
                    v___x_2715_ = lean_box(0);
                    v___x_2716_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2716_, 0, v_u_2712_);
                    lean_ctor_set(v___x_2716_, 1, v___x_2715_);
                    lean_inc_ref(v___x_2716_);
                    v___x_2717_ = l_Lean_mkConst(v___x_2714_, v___x_2716_);
                    v___x_2718_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__3;
                    v___x_2719_ = l_Lean_mkConst(v___x_2718_, v___x_2716_);
                    v___x_2720_ = l_Lean_mkAppB(v___x_2719_, v_type_2711_, v_semiringInst_2713_);
                    v_expectedInst_2721_ = l_Lean_mkAppB(v___x_2717_, v_type_2711_, v___x_2720_);
                    v___x_2722_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__5;
                    v___x_2723_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___closed__7;
                    v___x_2724_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_2711_, v_u_2712_, v___x_2722_, v___x_2723_, v_expectedInst_2721_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
                    if lean_obj_tag(v___x_2724_) == 0 {
                        v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
                        lean_inc_n(v_a_2725_, 2);
                        lean_dec_ref_known(v___x_2724_, 1);
                        v___f_2726_ = lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6___lam__0 as *mut core::ffi::c_void, 2, 1);
                        lean_closure_set(v___f_2726_, 0, v_a_2725_);
                        v___x_2727_ =
                            l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
                                v___f_2726_,
                                v___y_2688_,
                                v___y_2689_,
                            );
                        if lean_obj_tag(v___x_2727_) == 0 {
                            v_isSharedCheck_2734_ = (!lean_is_exclusive(v___x_2727_)) as u8;
                            if v_isSharedCheck_2734_ == 0 {
                                v_unused_2735_ = lean_ctor_get(v___x_2727_, 0);
                                lean_dec(v_unused_2735_);
                                v___x_2729_ = v___x_2727_;
                                v_isShared_2730_ = v_isSharedCheck_2734_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_2727_);
                                v___x_2729_ = lean_box(0);
                                v_isShared_2730_ = v_isSharedCheck_2734_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2725_);
                            v_a_2736_ = lean_ctor_get(v___x_2727_, 0);
                            v_isSharedCheck_2743_ = (!lean_is_exclusive(v___x_2727_)) as u8;
                            if v_isSharedCheck_2743_ == 0 {
                                v___x_2738_ = v___x_2727_;
                                v_isShared_2739_ = v_isSharedCheck_2743_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_2736_);
                                lean_dec(v___x_2727_);
                                v___x_2738_ = lean_box(0);
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
                    lean_ctor_set(v___x_2729_, 0, v_a_2725_);
                    v___x_2732_ = v___x_2729_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2725_);
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
                    v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
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
                    v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
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
    mut v___y_2753_: *mut LeanObject,
    mut v___y_2754_: *mut LeanObject,
    mut v___y_2755_: *mut LeanObject,
    mut v___y_2756_: *mut LeanObject,
    mut v___y_2757_: *mut LeanObject,
    mut v___y_2758_: *mut LeanObject,
    mut v___y_2759_: *mut LeanObject,
    mut v___y_2760_: *mut LeanObject,
    mut v___y_2761_: *mut LeanObject,
    mut v___y_2762_: *mut LeanObject,
    mut v___y_2763_: *mut LeanObject,
    mut v___y_2764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2765_: *mut LeanObject = core::ptr::null_mut();
    v_res_2765_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
    lean_dec(v___y_2763_);
    lean_dec_ref(v___y_2762_);
    lean_dec(v___y_2761_);
    lean_dec_ref(v___y_2760_);
    lean_dec(v___y_2759_);
    lean_dec_ref(v___y_2758_);
    lean_dec(v___y_2757_);
    lean_dec_ref(v___y_2756_);
    lean_dec(v___y_2755_);
    lean_dec(v___y_2754_);
    lean_dec_ref(v___y_2753_);
    return v_res_2765_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0(
    mut v_a_2766_: *mut LeanObject,
    mut v_s_2767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toRing_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextId_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_queue_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_basis_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recheck_2782_: u8 = 0;
    let mut v_invSet_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_2786_: u8 = 0;
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2789_: u8 = 0;
    let mut v_id_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denote_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2808_: u8 = 0;
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2816_: u8 = 0;
    let mut v_unused_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2818_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2768_ = lean_ctor_get(v_s_2767_, 0);
                v_invFn_x3f_2769_ = lean_ctor_get(v_s_2767_, 1);
                v_semiringId_x3f_2770_ = lean_ctor_get(v_s_2767_, 2);
                v_commSemiringInst_2771_ = lean_ctor_get(v_s_2767_, 3);
                v_commRingInst_2772_ = lean_ctor_get(v_s_2767_, 4);
                v_noZeroDivInst_x3f_2773_ = lean_ctor_get(v_s_2767_, 5);
                v_fieldInst_x3f_2774_ = lean_ctor_get(v_s_2767_, 6);
                v_powIdentityInst_x3f_2775_ = lean_ctor_get(v_s_2767_, 7);
                v_denoteEntries_2776_ = lean_ctor_get(v_s_2767_, 8);
                v_nextId_2777_ = lean_ctor_get(v_s_2767_, 9);
                v_steps_2778_ = lean_ctor_get(v_s_2767_, 10);
                v_queue_2779_ = lean_ctor_get(v_s_2767_, 11);
                v_basis_2780_ = lean_ctor_get(v_s_2767_, 12);
                v_diseqs_2781_ = lean_ctor_get(v_s_2767_, 13);
                v_recheck_2782_ = lean_ctor_get_uint8(
                    v_s_2767_,
                    (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                );
                v_invSet_2783_ = lean_ctor_get(v_s_2767_, 14);
                v_powIdentityVarCount_2784_ = lean_ctor_get(v_s_2767_, 15);
                v_numEq0_x3f_2785_ = lean_ctor_get(v_s_2767_, 16);
                v_numEq0Updated_2786_ = lean_ctor_get_uint8(
                    v_s_2767_,
                    (core::mem::size_of::<*mut LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_2818_ = (!lean_is_exclusive(v_s_2767_)) as u8;
                if v_isSharedCheck_2818_ == 0 {
                    v___x_2788_ = v_s_2767_;
                    v_isShared_2789_ = v_isSharedCheck_2818_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_numEq0_x3f_2785_);
                    lean_inc(v_powIdentityVarCount_2784_);
                    lean_inc(v_invSet_2783_);
                    lean_inc(v_diseqs_2781_);
                    lean_inc(v_basis_2780_);
                    lean_inc(v_queue_2779_);
                    lean_inc(v_steps_2778_);
                    lean_inc(v_nextId_2777_);
                    lean_inc(v_denoteEntries_2776_);
                    lean_inc(v_powIdentityInst_x3f_2775_);
                    lean_inc(v_fieldInst_x3f_2774_);
                    lean_inc(v_noZeroDivInst_x3f_2773_);
                    lean_inc(v_commRingInst_2772_);
                    lean_inc(v_commSemiringInst_2771_);
                    lean_inc(v_semiringId_x3f_2770_);
                    lean_inc(v_invFn_x3f_2769_);
                    lean_inc(v_toRing_2768_);
                    lean_dec(v_s_2767_);
                    v___x_2788_ = lean_box(0);
                    v_isShared_2789_ = v_isSharedCheck_2818_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_2790_ = lean_ctor_get(v_toRing_2768_, 0);
                v_type_2791_ = lean_ctor_get(v_toRing_2768_, 1);
                v_u_2792_ = lean_ctor_get(v_toRing_2768_, 2);
                v_ringInst_2793_ = lean_ctor_get(v_toRing_2768_, 3);
                v_semiringInst_2794_ = lean_ctor_get(v_toRing_2768_, 4);
                v_charInst_x3f_2795_ = lean_ctor_get(v_toRing_2768_, 5);
                v_addFn_x3f_2796_ = lean_ctor_get(v_toRing_2768_, 6);
                v_subFn_x3f_2797_ = lean_ctor_get(v_toRing_2768_, 8);
                v_negFn_x3f_2798_ = lean_ctor_get(v_toRing_2768_, 9);
                v_powFn_x3f_2799_ = lean_ctor_get(v_toRing_2768_, 10);
                v_intCastFn_x3f_2800_ = lean_ctor_get(v_toRing_2768_, 11);
                v_natCastFn_x3f_2801_ = lean_ctor_get(v_toRing_2768_, 12);
                v_one_x3f_2802_ = lean_ctor_get(v_toRing_2768_, 13);
                v_vars_2803_ = lean_ctor_get(v_toRing_2768_, 14);
                v_varMap_2804_ = lean_ctor_get(v_toRing_2768_, 15);
                v_denote_2805_ = lean_ctor_get(v_toRing_2768_, 16);
                v_isSharedCheck_2816_ = (!lean_is_exclusive(v_toRing_2768_)) as u8;
                if v_isSharedCheck_2816_ == 0 {
                    v_unused_2817_ = lean_ctor_get(v_toRing_2768_, 7);
                    lean_dec(v_unused_2817_);
                    v___x_2807_ = v_toRing_2768_;
                    v_isShared_2808_ = v_isSharedCheck_2816_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_denote_2805_);
                    lean_inc(v_varMap_2804_);
                    lean_inc(v_vars_2803_);
                    lean_inc(v_one_x3f_2802_);
                    lean_inc(v_natCastFn_x3f_2801_);
                    lean_inc(v_intCastFn_x3f_2800_);
                    lean_inc(v_powFn_x3f_2799_);
                    lean_inc(v_negFn_x3f_2798_);
                    lean_inc(v_subFn_x3f_2797_);
                    lean_inc(v_addFn_x3f_2796_);
                    lean_inc(v_charInst_x3f_2795_);
                    lean_inc(v_semiringInst_2794_);
                    lean_inc(v_ringInst_2793_);
                    lean_inc(v_u_2792_);
                    lean_inc(v_type_2791_);
                    lean_inc(v_id_2790_);
                    lean_dec(v_toRing_2768_);
                    v___x_2807_ = lean_box(0);
                    v_isShared_2808_ = v_isSharedCheck_2816_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2809_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2809_, 0, v_a_2766_);
                if v_isShared_2808_ == 0 {
                    lean_ctor_set(v___x_2807_, 7, v___x_2809_);
                    v___x_2811_ = v___x_2807_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 17, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_id_2790_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 1, v_type_2791_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 2, v_u_2792_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 3, v_ringInst_2793_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 4, v_semiringInst_2794_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 5, v_charInst_x3f_2795_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 6, v_addFn_x3f_2796_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 7, v___x_2809_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 8, v_subFn_x3f_2797_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 9, v_negFn_x3f_2798_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 10, v_powFn_x3f_2799_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 11, v_intCastFn_x3f_2800_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 12, v_natCastFn_x3f_2801_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 13, v_one_x3f_2802_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 14, v_vars_2803_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 15, v_varMap_2804_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 16, v_denote_2805_);
                    v___x_2811_ = v_reuseFailAlloc_2815_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2789_ == 0 {
                    lean_ctor_set(v___x_2788_, 0, v___x_2811_);
                    v___x_2813_ = v___x_2788_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 17, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2811_);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_invFn_x3f_2769_);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 2, v_semiringId_x3f_2770_);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 3, v_commSemiringInst_2771_);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 4, v_commRingInst_2772_);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 5, v_noZeroDivInst_x3f_2773_);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 6, v_fieldInst_x3f_2774_);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 7, v_powIdentityInst_x3f_2775_);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 8, v_denoteEntries_2776_);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 9, v_nextId_2777_);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 10, v_steps_2778_);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 11, v_queue_2779_);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 12, v_basis_2780_);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 13, v_diseqs_2781_);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 14, v_invSet_2783_);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 15, v_powIdentityVarCount_2784_);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 16, v_numEq0_x3f_2785_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2814_,
                        (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                        v_recheck_2782_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2814_,
                        (core::mem::size_of::<*mut LeanObject>() * 17 + 1) as u32,
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
    mut v___y_2830_: *mut LeanObject,
    mut v___y_2831_: *mut LeanObject,
    mut v___y_2832_: *mut LeanObject,
    mut v___y_2833_: *mut LeanObject,
    mut v___y_2834_: *mut LeanObject,
    mut v___y_2835_: *mut LeanObject,
    mut v___y_2836_: *mut LeanObject,
    mut v___y_2837_: *mut LeanObject,
    mut v___y_2838_: *mut LeanObject,
    mut v___y_2839_: *mut LeanObject,
    mut v___y_2840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2846_: u8 = 0;
    let mut v_toRing_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expectedInst_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2872_: u8 = 0;
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2876_: u8 = 0;
    let mut v_unused_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2881_: u8 = 0;
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2885_: u8 = 0;
    let mut v_isSharedCheck_2886_: u8 = 0;
    let mut v_a_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2890_: u8 = 0;
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2893_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2842_) == 0 {
                    v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
                    v_isSharedCheck_2886_ = (!lean_is_exclusive(v___x_2842_)) as u8;
                    if v_isSharedCheck_2886_ == 0 {
                        v___x_2845_ = v___x_2842_;
                        v_isShared_2846_ = v_isSharedCheck_2886_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2843_);
                        lean_dec(v___x_2842_);
                        v___x_2845_ = lean_box(0);
                        v_isShared_2846_ = v_isSharedCheck_2886_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2887_ = lean_ctor_get(v___x_2842_, 0);
                    v_isSharedCheck_2894_ = (!lean_is_exclusive(v___x_2842_)) as u8;
                    if v_isSharedCheck_2894_ == 0 {
                        v___x_2889_ = v___x_2842_;
                        v_isShared_2890_ = v_isSharedCheck_2894_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2887_);
                        lean_dec(v___x_2842_);
                        v___x_2889_ = lean_box(0);
                        v_isShared_2890_ = v_isSharedCheck_2894_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_2847_ = lean_ctor_get(v_a_2843_, 0);
                lean_inc_ref(v_toRing_2847_);
                lean_dec(v_a_2843_);
                v_mulFn_x3f_2848_ = lean_ctor_get(v_toRing_2847_, 7);
                if lean_obj_tag(v_mulFn_x3f_2848_) == 1 {
                    lean_inc_ref(v_mulFn_x3f_2848_);
                    lean_dec_ref(v_toRing_2847_);
                    v_val_2849_ = lean_ctor_get(v_mulFn_x3f_2848_, 0);
                    lean_inc(v_val_2849_);
                    lean_dec_ref_known(v_mulFn_x3f_2848_, 1);
                    if v_isShared_2846_ == 0 {
                        lean_ctor_set(v___x_2845_, 0, v_val_2849_);
                        v___x_2851_ = v___x_2845_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_val_2849_);
                        v___x_2851_ = v_reuseFailAlloc_2852_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2845_);
                    v_type_2853_ = lean_ctor_get(v_toRing_2847_, 1);
                    lean_inc_ref_n(v_type_2853_, 3);
                    v_u_2854_ = lean_ctor_get(v_toRing_2847_, 2);
                    lean_inc_n(v_u_2854_, 2);
                    v_semiringInst_2855_ = lean_ctor_get(v_toRing_2847_, 4);
                    lean_inc_ref(v_semiringInst_2855_);
                    lean_dec_ref(v_toRing_2847_);
                    v___x_2856_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__1;
                    v___x_2857_ = lean_box(0);
                    v___x_2858_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2858_, 0, v_u_2854_);
                    lean_ctor_set(v___x_2858_, 1, v___x_2857_);
                    lean_inc_ref(v___x_2858_);
                    v___x_2859_ = l_Lean_mkConst(v___x_2856_, v___x_2858_);
                    v___x_2860_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__3;
                    v___x_2861_ = l_Lean_mkConst(v___x_2860_, v___x_2858_);
                    v___x_2862_ = l_Lean_mkAppB(v___x_2861_, v_type_2853_, v_semiringInst_2855_);
                    v_expectedInst_2863_ = l_Lean_mkAppB(v___x_2859_, v_type_2853_, v___x_2862_);
                    v___x_2864_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___closed__4;
                    v___x_2865_ = l_Int_Linear_Poly_isNonlinear___redArg___closed__2;
                    v___x_2866_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3_spec__7(v_type_2853_, v_u_2854_, v___x_2864_, v___x_2865_, v_expectedInst_2863_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
                    if lean_obj_tag(v___x_2866_) == 0 {
                        v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
                        lean_inc_n(v_a_2867_, 2);
                        lean_dec_ref_known(v___x_2866_, 1);
                        v___f_2868_ = lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3___lam__0 as *mut core::ffi::c_void, 2, 1);
                        lean_closure_set(v___f_2868_, 0, v_a_2867_);
                        v___x_2869_ =
                            l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
                                v___f_2868_,
                                v___y_2830_,
                                v___y_2831_,
                            );
                        if lean_obj_tag(v___x_2869_) == 0 {
                            v_isSharedCheck_2876_ = (!lean_is_exclusive(v___x_2869_)) as u8;
                            if v_isSharedCheck_2876_ == 0 {
                                v_unused_2877_ = lean_ctor_get(v___x_2869_, 0);
                                lean_dec(v_unused_2877_);
                                v___x_2871_ = v___x_2869_;
                                v_isShared_2872_ = v_isSharedCheck_2876_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_2869_);
                                v___x_2871_ = lean_box(0);
                                v_isShared_2872_ = v_isSharedCheck_2876_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2867_);
                            v_a_2878_ = lean_ctor_get(v___x_2869_, 0);
                            v_isSharedCheck_2885_ = (!lean_is_exclusive(v___x_2869_)) as u8;
                            if v_isSharedCheck_2885_ == 0 {
                                v___x_2880_ = v___x_2869_;
                                v_isShared_2881_ = v_isSharedCheck_2885_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_2878_);
                                lean_dec(v___x_2869_);
                                v___x_2880_ = lean_box(0);
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
                    lean_ctor_set(v___x_2871_, 0, v_a_2867_);
                    v___x_2874_ = v___x_2871_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2867_);
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
                    v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
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
                    v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
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
    mut v___y_2895_: *mut LeanObject,
    mut v___y_2896_: *mut LeanObject,
    mut v___y_2897_: *mut LeanObject,
    mut v___y_2898_: *mut LeanObject,
    mut v___y_2899_: *mut LeanObject,
    mut v___y_2900_: *mut LeanObject,
    mut v___y_2901_: *mut LeanObject,
    mut v___y_2902_: *mut LeanObject,
    mut v___y_2903_: *mut LeanObject,
    mut v___y_2904_: *mut LeanObject,
    mut v___y_2905_: *mut LeanObject,
    mut v___y_2906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2907_: *mut LeanObject = core::ptr::null_mut();
    v_res_2907_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
    lean_dec(v___y_2905_);
    lean_dec_ref(v___y_2904_);
    lean_dec(v___y_2903_);
    lean_dec_ref(v___y_2902_);
    lean_dec(v___y_2901_);
    lean_dec_ref(v___y_2900_);
    lean_dec(v___y_2899_);
    lean_dec_ref(v___y_2898_);
    lean_dec(v___y_2897_);
    lean_dec(v___y_2896_);
    lean_dec_ref(v___y_2895_);
    return v_res_2907_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0(
    mut v_a_2908_: *mut LeanObject,
    mut v_s_2909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toRing_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextId_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_queue_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_basis_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recheck_2924_: u8 = 0;
    let mut v_invSet_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_2928_: u8 = 0;
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v_id_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denote_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2950_: u8 = 0;
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2958_: u8 = 0;
    let mut v_unused_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2960_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2910_ = lean_ctor_get(v_s_2909_, 0);
                v_invFn_x3f_2911_ = lean_ctor_get(v_s_2909_, 1);
                v_semiringId_x3f_2912_ = lean_ctor_get(v_s_2909_, 2);
                v_commSemiringInst_2913_ = lean_ctor_get(v_s_2909_, 3);
                v_commRingInst_2914_ = lean_ctor_get(v_s_2909_, 4);
                v_noZeroDivInst_x3f_2915_ = lean_ctor_get(v_s_2909_, 5);
                v_fieldInst_x3f_2916_ = lean_ctor_get(v_s_2909_, 6);
                v_powIdentityInst_x3f_2917_ = lean_ctor_get(v_s_2909_, 7);
                v_denoteEntries_2918_ = lean_ctor_get(v_s_2909_, 8);
                v_nextId_2919_ = lean_ctor_get(v_s_2909_, 9);
                v_steps_2920_ = lean_ctor_get(v_s_2909_, 10);
                v_queue_2921_ = lean_ctor_get(v_s_2909_, 11);
                v_basis_2922_ = lean_ctor_get(v_s_2909_, 12);
                v_diseqs_2923_ = lean_ctor_get(v_s_2909_, 13);
                v_recheck_2924_ = lean_ctor_get_uint8(
                    v_s_2909_,
                    (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                );
                v_invSet_2925_ = lean_ctor_get(v_s_2909_, 14);
                v_powIdentityVarCount_2926_ = lean_ctor_get(v_s_2909_, 15);
                v_numEq0_x3f_2927_ = lean_ctor_get(v_s_2909_, 16);
                v_numEq0Updated_2928_ = lean_ctor_get_uint8(
                    v_s_2909_,
                    (core::mem::size_of::<*mut LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_2960_ = (!lean_is_exclusive(v_s_2909_)) as u8;
                if v_isSharedCheck_2960_ == 0 {
                    v___x_2930_ = v_s_2909_;
                    v_isShared_2931_ = v_isSharedCheck_2960_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_numEq0_x3f_2927_);
                    lean_inc(v_powIdentityVarCount_2926_);
                    lean_inc(v_invSet_2925_);
                    lean_inc(v_diseqs_2923_);
                    lean_inc(v_basis_2922_);
                    lean_inc(v_queue_2921_);
                    lean_inc(v_steps_2920_);
                    lean_inc(v_nextId_2919_);
                    lean_inc(v_denoteEntries_2918_);
                    lean_inc(v_powIdentityInst_x3f_2917_);
                    lean_inc(v_fieldInst_x3f_2916_);
                    lean_inc(v_noZeroDivInst_x3f_2915_);
                    lean_inc(v_commRingInst_2914_);
                    lean_inc(v_commSemiringInst_2913_);
                    lean_inc(v_semiringId_x3f_2912_);
                    lean_inc(v_invFn_x3f_2911_);
                    lean_inc(v_toRing_2910_);
                    lean_dec(v_s_2909_);
                    v___x_2930_ = lean_box(0);
                    v_isShared_2931_ = v_isSharedCheck_2960_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_2932_ = lean_ctor_get(v_toRing_2910_, 0);
                v_type_2933_ = lean_ctor_get(v_toRing_2910_, 1);
                v_u_2934_ = lean_ctor_get(v_toRing_2910_, 2);
                v_ringInst_2935_ = lean_ctor_get(v_toRing_2910_, 3);
                v_semiringInst_2936_ = lean_ctor_get(v_toRing_2910_, 4);
                v_charInst_x3f_2937_ = lean_ctor_get(v_toRing_2910_, 5);
                v_addFn_x3f_2938_ = lean_ctor_get(v_toRing_2910_, 6);
                v_mulFn_x3f_2939_ = lean_ctor_get(v_toRing_2910_, 7);
                v_subFn_x3f_2940_ = lean_ctor_get(v_toRing_2910_, 8);
                v_negFn_x3f_2941_ = lean_ctor_get(v_toRing_2910_, 9);
                v_intCastFn_x3f_2942_ = lean_ctor_get(v_toRing_2910_, 11);
                v_natCastFn_x3f_2943_ = lean_ctor_get(v_toRing_2910_, 12);
                v_one_x3f_2944_ = lean_ctor_get(v_toRing_2910_, 13);
                v_vars_2945_ = lean_ctor_get(v_toRing_2910_, 14);
                v_varMap_2946_ = lean_ctor_get(v_toRing_2910_, 15);
                v_denote_2947_ = lean_ctor_get(v_toRing_2910_, 16);
                v_isSharedCheck_2958_ = (!lean_is_exclusive(v_toRing_2910_)) as u8;
                if v_isSharedCheck_2958_ == 0 {
                    v_unused_2959_ = lean_ctor_get(v_toRing_2910_, 10);
                    lean_dec(v_unused_2959_);
                    v___x_2949_ = v_toRing_2910_;
                    v_isShared_2950_ = v_isSharedCheck_2958_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_denote_2947_);
                    lean_inc(v_varMap_2946_);
                    lean_inc(v_vars_2945_);
                    lean_inc(v_one_x3f_2944_);
                    lean_inc(v_natCastFn_x3f_2943_);
                    lean_inc(v_intCastFn_x3f_2942_);
                    lean_inc(v_negFn_x3f_2941_);
                    lean_inc(v_subFn_x3f_2940_);
                    lean_inc(v_mulFn_x3f_2939_);
                    lean_inc(v_addFn_x3f_2938_);
                    lean_inc(v_charInst_x3f_2937_);
                    lean_inc(v_semiringInst_2936_);
                    lean_inc(v_ringInst_2935_);
                    lean_inc(v_u_2934_);
                    lean_inc(v_type_2933_);
                    lean_inc(v_id_2932_);
                    lean_dec(v_toRing_2910_);
                    v___x_2949_ = lean_box(0);
                    v_isShared_2950_ = v_isSharedCheck_2958_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2951_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2951_, 0, v_a_2908_);
                if v_isShared_2950_ == 0 {
                    lean_ctor_set(v___x_2949_, 10, v___x_2951_);
                    v___x_2953_ = v___x_2949_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 17, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_id_2932_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_type_2933_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 2, v_u_2934_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 3, v_ringInst_2935_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 4, v_semiringInst_2936_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 5, v_charInst_x3f_2937_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 6, v_addFn_x3f_2938_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 7, v_mulFn_x3f_2939_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 8, v_subFn_x3f_2940_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 9, v_negFn_x3f_2941_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 10, v___x_2951_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 11, v_intCastFn_x3f_2942_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 12, v_natCastFn_x3f_2943_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 13, v_one_x3f_2944_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 14, v_vars_2945_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 15, v_varMap_2946_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 16, v_denote_2947_);
                    v___x_2953_ = v_reuseFailAlloc_2957_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2931_ == 0 {
                    lean_ctor_set(v___x_2930_, 0, v___x_2953_);
                    v___x_2955_ = v___x_2930_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 17, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2953_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_invFn_x3f_2911_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 2, v_semiringId_x3f_2912_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 3, v_commSemiringInst_2913_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 4, v_commRingInst_2914_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 5, v_noZeroDivInst_x3f_2915_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 6, v_fieldInst_x3f_2916_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 7, v_powIdentityInst_x3f_2917_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 8, v_denoteEntries_2918_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 9, v_nextId_2919_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 10, v_steps_2920_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 11, v_queue_2921_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 12, v_basis_2922_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 13, v_diseqs_2923_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 14, v_invSet_2925_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 15, v_powIdentityVarCount_2926_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 16, v_numEq0_x3f_2927_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2956_,
                        (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                        v_recheck_2924_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2956_,
                        (core::mem::size_of::<*mut LeanObject>() * 17 + 1) as u32,
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
-> *mut LeanObject {
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    v___x_2963_ = lean_unsigned_to_nat(0);
    v___x_2964_ = l_Lean_Level_ofNat(v___x_2963_);
    return v___x_2964_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(
    mut v_u_2971_: *mut LeanObject,
    mut v_type_2972_: *mut LeanObject,
    mut v_semiringInst_2973_: *mut LeanObject,
    mut v___y_2974_: *mut LeanObject,
    mut v___y_2975_: *mut LeanObject,
    mut v___y_2976_: *mut LeanObject,
    mut v___y_2977_: *mut LeanObject,
    mut v___y_2978_: *mut LeanObject,
    mut v___y_2979_: *mut LeanObject,
    mut v___y_2980_: *mut LeanObject,
    mut v___y_2981_: *mut LeanObject,
    mut v___y_2982_: *mut LeanObject,
    mut v___y_2983_: *mut LeanObject,
    mut v___y_2984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3010_: u8 = 0;
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2986_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__0;
                v___x_2987_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1_once), _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__1);
                v___x_2988_ = lean_box(0);
                lean_inc(v_u_2971_);
                v___x_2989_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2989_, 0, v_u_2971_);
                lean_ctor_set(v___x_2989_, 1, v___x_2988_);
                lean_inc_ref(v___x_2989_);
                v___x_2990_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2990_, 0, v___x_2987_);
                lean_ctor_set(v___x_2990_, 1, v___x_2989_);
                v___x_2991_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2991_, 0, v_u_2971_);
                lean_ctor_set(v___x_2991_, 1, v___x_2990_);
                lean_inc_ref(v___x_2991_);
                v___x_2992_ = l_Lean_mkConst(v___x_2986_, v___x_2991_);
                v___x_2993_ = l_Lean_Nat_mkType;
                lean_inc_ref_n(v_type_2972_, 2);
                v___x_2994_ = l_Lean_mkApp3(v___x_2992_, v_type_2972_, v___x_2993_, v_type_2972_);
                v___x_2995_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7(v___x_2994_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
                if lean_obj_tag(v___x_2995_) == 0 {
                    v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
                    lean_inc_n(v_a_2996_, 2);
                    lean_dec_ref_known(v___x_2995_, 1);
                    v___x_2997_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15___closed__3;
                    v___x_2998_ = l_Lean_mkConst(v___x_2997_, v___x_2989_);
                    lean_inc_ref(v_type_2972_);
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
                    if lean_obj_tag(v___x_3001_) == 0 {
                        lean_dec_ref_known(v___x_3001_, 1);
                        v___x_3002_ = l_Lean_mkConst(v___x_3000_, v___x_2991_);
                        lean_inc_ref(v_type_2972_);
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
                        if lean_obj_tag(v___x_3004_) == 0 {
                            v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
                            lean_inc(v_a_3005_);
                            lean_dec_ref_known(v___x_3004_, 1);
                            v___x_3006_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_3005_, v___y_2980_);
                            return v___x_3006_;
                        } else {
                            return v___x_3004_;
                        }
                    } else {
                        lean_dec(v_a_2996_);
                        lean_dec_ref_known(v___x_2991_, 2);
                        lean_dec_ref(v_type_2972_);
                        v_a_3007_ = lean_ctor_get(v___x_3001_, 0);
                        v_isSharedCheck_3014_ = (!lean_is_exclusive(v___x_3001_)) as u8;
                        if v_isSharedCheck_3014_ == 0 {
                            v___x_3009_ = v___x_3001_;
                            v_isShared_3010_ = v_isSharedCheck_3014_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3007_);
                            lean_dec(v___x_3001_);
                            v___x_3009_ = lean_box(0);
                            v_isShared_3010_ = v_isSharedCheck_3014_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_2991_, 2);
                    lean_dec_ref_known(v___x_2989_, 2);
                    lean_dec_ref(v_semiringInst_2973_);
                    lean_dec_ref(v_type_2972_);
                    return v___x_2995_;
                }
            }
            1 => {
                if v_isShared_3010_ == 0 {
                    v___x_3012_ = v___x_3009_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
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
    mut v_u_3015_: *mut LeanObject,
    mut v_type_3016_: *mut LeanObject,
    mut v_semiringInst_3017_: *mut LeanObject,
    mut v___y_3018_: *mut LeanObject,
    mut v___y_3019_: *mut LeanObject,
    mut v___y_3020_: *mut LeanObject,
    mut v___y_3021_: *mut LeanObject,
    mut v___y_3022_: *mut LeanObject,
    mut v___y_3023_: *mut LeanObject,
    mut v___y_3024_: *mut LeanObject,
    mut v___y_3025_: *mut LeanObject,
    mut v___y_3026_: *mut LeanObject,
    mut v___y_3027_: *mut LeanObject,
    mut v___y_3028_: *mut LeanObject,
    mut v___y_3029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3030_: *mut LeanObject = core::ptr::null_mut();
    v_res_3030_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_3015_, v_type_3016_, v_semiringInst_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
    lean_dec(v___y_3028_);
    lean_dec_ref(v___y_3027_);
    lean_dec(v___y_3026_);
    lean_dec_ref(v___y_3025_);
    lean_dec(v___y_3024_);
    lean_dec_ref(v___y_3023_);
    lean_dec(v___y_3022_);
    lean_dec_ref(v___y_3021_);
    lean_dec(v___y_3020_);
    lean_dec(v___y_3019_);
    lean_dec_ref(v___y_3018_);
    return v_res_3030_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(
    mut v___y_3031_: *mut LeanObject,
    mut v___y_3032_: *mut LeanObject,
    mut v___y_3033_: *mut LeanObject,
    mut v___y_3034_: *mut LeanObject,
    mut v___y_3035_: *mut LeanObject,
    mut v___y_3036_: *mut LeanObject,
    mut v___y_3037_: *mut LeanObject,
    mut v___y_3038_: *mut LeanObject,
    mut v___y_3039_: *mut LeanObject,
    mut v___y_3040_: *mut LeanObject,
    mut v___y_3041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3047_: u8 = 0;
    let mut v_toRing_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3063_: u8 = 0;
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3067_: u8 = 0;
    let mut v_unused_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3072_: u8 = 0;
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3076_: u8 = 0;
    let mut v_isSharedCheck_3077_: u8 = 0;
    let mut v_a_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3081_: u8 = 0;
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3084_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_3043_) == 0 {
                    v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
                    v_isSharedCheck_3077_ = (!lean_is_exclusive(v___x_3043_)) as u8;
                    if v_isSharedCheck_3077_ == 0 {
                        v___x_3046_ = v___x_3043_;
                        v_isShared_3047_ = v_isSharedCheck_3077_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3044_);
                        lean_dec(v___x_3043_);
                        v___x_3046_ = lean_box(0);
                        v_isShared_3047_ = v_isSharedCheck_3077_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3078_ = lean_ctor_get(v___x_3043_, 0);
                    v_isSharedCheck_3085_ = (!lean_is_exclusive(v___x_3043_)) as u8;
                    if v_isSharedCheck_3085_ == 0 {
                        v___x_3080_ = v___x_3043_;
                        v_isShared_3081_ = v_isSharedCheck_3085_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3078_);
                        lean_dec(v___x_3043_);
                        v___x_3080_ = lean_box(0);
                        v_isShared_3081_ = v_isSharedCheck_3085_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_3048_ = lean_ctor_get(v_a_3044_, 0);
                lean_inc_ref(v_toRing_3048_);
                lean_dec(v_a_3044_);
                v_powFn_x3f_3049_ = lean_ctor_get(v_toRing_3048_, 10);
                if lean_obj_tag(v_powFn_x3f_3049_) == 1 {
                    lean_inc_ref(v_powFn_x3f_3049_);
                    lean_dec_ref(v_toRing_3048_);
                    v_val_3050_ = lean_ctor_get(v_powFn_x3f_3049_, 0);
                    lean_inc(v_val_3050_);
                    lean_dec_ref_known(v_powFn_x3f_3049_, 1);
                    if v_isShared_3047_ == 0 {
                        lean_ctor_set(v___x_3046_, 0, v_val_3050_);
                        v___x_3052_ = v___x_3046_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_val_3050_);
                        v___x_3052_ = v_reuseFailAlloc_3053_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3046_);
                    v_type_3054_ = lean_ctor_get(v_toRing_3048_, 1);
                    lean_inc_ref(v_type_3054_);
                    v_u_3055_ = lean_ctor_get(v_toRing_3048_, 2);
                    lean_inc(v_u_3055_);
                    v_semiringInst_3056_ = lean_ctor_get(v_toRing_3048_, 4);
                    lean_inc_ref(v_semiringInst_3056_);
                    lean_dec_ref(v_toRing_3048_);
                    v___x_3057_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12_spec__15(v_u_3055_, v_type_3054_, v_semiringInst_3056_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
                    if lean_obj_tag(v___x_3057_) == 0 {
                        v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
                        lean_inc_n(v_a_3058_, 2);
                        lean_dec_ref_known(v___x_3057_, 1);
                        v___f_3059_ = lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12___lam__0 as *mut core::ffi::c_void, 2, 1);
                        lean_closure_set(v___f_3059_, 0, v_a_3058_);
                        v___x_3060_ =
                            l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
                                v___f_3059_,
                                v___y_3031_,
                                v___y_3032_,
                            );
                        if lean_obj_tag(v___x_3060_) == 0 {
                            v_isSharedCheck_3067_ = (!lean_is_exclusive(v___x_3060_)) as u8;
                            if v_isSharedCheck_3067_ == 0 {
                                v_unused_3068_ = lean_ctor_get(v___x_3060_, 0);
                                lean_dec(v_unused_3068_);
                                v___x_3062_ = v___x_3060_;
                                v_isShared_3063_ = v_isSharedCheck_3067_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_3060_);
                                v___x_3062_ = lean_box(0);
                                v_isShared_3063_ = v_isSharedCheck_3067_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3058_);
                            v_a_3069_ = lean_ctor_get(v___x_3060_, 0);
                            v_isSharedCheck_3076_ = (!lean_is_exclusive(v___x_3060_)) as u8;
                            if v_isSharedCheck_3076_ == 0 {
                                v___x_3071_ = v___x_3060_;
                                v_isShared_3072_ = v_isSharedCheck_3076_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3069_);
                                lean_dec(v___x_3060_);
                                v___x_3071_ = lean_box(0);
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
                    lean_ctor_set(v___x_3062_, 0, v_a_3058_);
                    v___x_3065_ = v___x_3062_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3058_);
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
                    v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
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
                    v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
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
    mut v___y_3086_: *mut LeanObject,
    mut v___y_3087_: *mut LeanObject,
    mut v___y_3088_: *mut LeanObject,
    mut v___y_3089_: *mut LeanObject,
    mut v___y_3090_: *mut LeanObject,
    mut v___y_3091_: *mut LeanObject,
    mut v___y_3092_: *mut LeanObject,
    mut v___y_3093_: *mut LeanObject,
    mut v___y_3094_: *mut LeanObject,
    mut v___y_3095_: *mut LeanObject,
    mut v___y_3096_: *mut LeanObject,
    mut v___y_3097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3098_: *mut LeanObject = core::ptr::null_mut();
    v_res_3098_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
    lean_dec(v___y_3096_);
    lean_dec_ref(v___y_3095_);
    lean_dec(v___y_3094_);
    lean_dec_ref(v___y_3093_);
    lean_dec(v___y_3092_);
    lean_dec_ref(v___y_3091_);
    lean_dec(v___y_3090_);
    lean_dec_ref(v___y_3089_);
    lean_dec(v___y_3088_);
    lean_dec(v___y_3087_);
    lean_dec_ref(v___y_3086_);
    return v_res_3098_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(
    mut v_pw_3099_: *mut LeanObject,
    mut v___y_3100_: *mut LeanObject,
    mut v___y_3101_: *mut LeanObject,
    mut v___y_3102_: *mut LeanObject,
    mut v___y_3103_: *mut LeanObject,
    mut v___y_3104_: *mut LeanObject,
    mut v___y_3105_: *mut LeanObject,
    mut v___y_3106_: *mut LeanObject,
    mut v___y_3107_: *mut LeanObject,
    mut v___y_3108_: *mut LeanObject,
    mut v___y_3109_: *mut LeanObject,
    mut v___y_3110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3116_: u8 = 0;
    let mut v_toRing_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: u8 = 0;
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3129_: u8 = 0;
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3135_: u8 = 0;
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: u8 = 0;
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3144_: u8 = 0;
    let mut v_a_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3148_: u8 = 0;
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3151_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_3112_) == 0 {
                    v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
                    v_isSharedCheck_3144_ = (!lean_is_exclusive(v___x_3112_)) as u8;
                    if v_isSharedCheck_3144_ == 0 {
                        v___x_3115_ = v___x_3112_;
                        v_isShared_3116_ = v_isSharedCheck_3144_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3113_);
                        lean_dec(v___x_3112_);
                        v___x_3115_ = lean_box(0);
                        v_isShared_3116_ = v_isSharedCheck_3144_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_pw_3099_);
                    v_a_3145_ = lean_ctor_get(v___x_3112_, 0);
                    v_isSharedCheck_3152_ = (!lean_is_exclusive(v___x_3112_)) as u8;
                    if v_isSharedCheck_3152_ == 0 {
                        v___x_3147_ = v___x_3112_;
                        v_isShared_3148_ = v_isSharedCheck_3152_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3145_);
                        lean_dec(v___x_3112_);
                        v___x_3147_ = lean_box(0);
                        v_isShared_3148_ = v_isSharedCheck_3152_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_3117_ = lean_ctor_get(v_a_3113_, 0);
                lean_inc_ref(v_toRing_3117_);
                lean_dec(v_a_3113_);
                v_vars_3118_ = lean_ctor_get(v_toRing_3117_, 14);
                lean_inc_ref(v_vars_3118_);
                lean_dec_ref(v_toRing_3117_);
                v_x_3119_ = lean_ctor_get(v_pw_3099_, 0);
                lean_inc(v_x_3119_);
                v_k_3120_ = lean_ctor_get(v_pw_3099_, 1);
                lean_inc(v_k_3120_);
                lean_dec_ref(v_pw_3099_);
                v_size_3139_ = lean_ctor_get(v_vars_3118_, 2);
                v___x_3140_ = l_Lean_instInhabitedExpr;
                v___x_3141_ = lean_nat_dec_lt(v_x_3119_, v_size_3139_);
                if v___x_3141_ == 0 {
                    lean_dec(v_x_3119_);
                    lean_dec_ref(v_vars_3118_);
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
                    lean_dec(v_x_3119_);
                    lean_dec_ref(v_vars_3118_);
                    v___y_3122_ = v___x_3143_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3123_ = lean_unsigned_to_nat(1);
                v___x_3124_ = lean_nat_dec_eq(v_k_3120_, v___x_3123_);
                if v___x_3124_ == 0 {
                    lean_del_object(v___x_3115_);
                    v___x_3125_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9_spec__12(v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
                    if lean_obj_tag(v___x_3125_) == 0 {
                        v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
                        v_isSharedCheck_3135_ = (!lean_is_exclusive(v___x_3125_)) as u8;
                        if v_isSharedCheck_3135_ == 0 {
                            v___x_3128_ = v___x_3125_;
                            v_isShared_3129_ = v_isSharedCheck_3135_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3126_);
                            lean_dec(v___x_3125_);
                            v___x_3128_ = lean_box(0);
                            v_isShared_3129_ = v_isSharedCheck_3135_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___y_3122_);
                        lean_dec(v_k_3120_);
                        return v___x_3125_;
                    }
                } else {
                    lean_dec(v_k_3120_);
                    if v_isShared_3116_ == 0 {
                        lean_ctor_set(v___x_3115_, 0, v___y_3122_);
                        v___x_3137_ = v___x_3115_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___y_3122_);
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
                    lean_ctor_set(v___x_3128_, 0, v___x_3131_);
                    v___x_3133_ = v___x_3128_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3131_);
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
                    v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
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
    mut v_pw_3153_: *mut LeanObject,
    mut v___y_3154_: *mut LeanObject,
    mut v___y_3155_: *mut LeanObject,
    mut v___y_3156_: *mut LeanObject,
    mut v___y_3157_: *mut LeanObject,
    mut v___y_3158_: *mut LeanObject,
    mut v___y_3159_: *mut LeanObject,
    mut v___y_3160_: *mut LeanObject,
    mut v___y_3161_: *mut LeanObject,
    mut v___y_3162_: *mut LeanObject,
    mut v___y_3163_: *mut LeanObject,
    mut v___y_3164_: *mut LeanObject,
    mut v___y_3165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3166_: *mut LeanObject = core::ptr::null_mut();
    v_res_3166_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_pw_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
    lean_dec(v___y_3164_);
    lean_dec_ref(v___y_3163_);
    lean_dec(v___y_3162_);
    lean_dec_ref(v___y_3161_);
    lean_dec(v___y_3160_);
    lean_dec_ref(v___y_3159_);
    lean_dec(v___y_3158_);
    lean_dec_ref(v___y_3157_);
    lean_dec(v___y_3156_);
    lean_dec(v___y_3155_);
    lean_dec_ref(v___y_3154_);
    return v_res_3166_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(
    mut v_m_3167_: *mut LeanObject,
    mut v_acc_3168_: *mut LeanObject,
    mut v___y_3169_: *mut LeanObject,
    mut v___y_3170_: *mut LeanObject,
    mut v___y_3171_: *mut LeanObject,
    mut v___y_3172_: *mut LeanObject,
    mut v___y_3173_: *mut LeanObject,
    mut v___y_3174_: *mut LeanObject,
    mut v___y_3175_: *mut LeanObject,
    mut v___y_3176_: *mut LeanObject,
    mut v___y_3177_: *mut LeanObject,
    mut v___y_3178_: *mut LeanObject,
    mut v___y_3179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_m_3167_) == 0 {
                    v___x_3181_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3181_, 0, v_acc_3168_);
                    return v___x_3181_;
                } else {
                    v_p_3182_ = lean_ctor_get(v_m_3167_, 0);
                    lean_inc_ref(v_p_3182_);
                    v_m_3183_ = lean_ctor_get(v_m_3167_, 1);
                    lean_inc(v_m_3183_);
                    lean_dec_ref_known(v_m_3167_, 2);
                    v___x_3184_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
                    if lean_obj_tag(v___x_3184_) == 0 {
                        v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
                        lean_inc(v_a_3185_);
                        lean_dec_ref_known(v___x_3184_, 1);
                        v___x_3186_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_3182_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
                        if lean_obj_tag(v___x_3186_) == 0 {
                            v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
                            lean_inc(v_a_3187_);
                            lean_dec_ref_known(v___x_3186_, 1);
                            v___x_3188_ = l_Lean_mkAppB(v_a_3185_, v_acc_3168_, v_a_3187_);
                            v_m_3167_ = v_m_3183_;
                            v_acc_3168_ = v___x_3188_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_a_3185_);
                            lean_dec(v_m_3183_);
                            lean_dec_ref(v_acc_3168_);
                            return v___x_3186_;
                        }
                    } else {
                        lean_dec(v_m_3183_);
                        lean_dec_ref(v_p_3182_);
                        lean_dec_ref(v_acc_3168_);
                        return v___x_3184_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10___boxed(
    mut v_m_3190_: *mut LeanObject,
    mut v_acc_3191_: *mut LeanObject,
    mut v___y_3192_: *mut LeanObject,
    mut v___y_3193_: *mut LeanObject,
    mut v___y_3194_: *mut LeanObject,
    mut v___y_3195_: *mut LeanObject,
    mut v___y_3196_: *mut LeanObject,
    mut v___y_3197_: *mut LeanObject,
    mut v___y_3198_: *mut LeanObject,
    mut v___y_3199_: *mut LeanObject,
    mut v___y_3200_: *mut LeanObject,
    mut v___y_3201_: *mut LeanObject,
    mut v___y_3202_: *mut LeanObject,
    mut v___y_3203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3204_: *mut LeanObject = core::ptr::null_mut();
    v_res_3204_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_m_3190_, v_acc_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
    lean_dec(v___y_3202_);
    lean_dec_ref(v___y_3201_);
    lean_dec(v___y_3200_);
    lean_dec_ref(v___y_3199_);
    lean_dec(v___y_3198_);
    lean_dec_ref(v___y_3197_);
    lean_dec(v___y_3196_);
    lean_dec_ref(v___y_3195_);
    lean_dec(v___y_3194_);
    lean_dec(v___y_3193_);
    lean_dec_ref(v___y_3192_);
    return v_res_3204_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0()
-> *mut LeanObject {
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    v___x_3205_ = lean_unsigned_to_nat(1);
    v___x_3206_ = lean_nat_to_int(v___x_3205_);
    return v___x_3206_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(
    mut v_m_3207_: *mut LeanObject,
    mut v___y_3208_: *mut LeanObject,
    mut v___y_3209_: *mut LeanObject,
    mut v___y_3210_: *mut LeanObject,
    mut v___y_3211_: *mut LeanObject,
    mut v___y_3212_: *mut LeanObject,
    mut v___y_3213_: *mut LeanObject,
    mut v___y_3214_: *mut LeanObject,
    mut v___y_3215_: *mut LeanObject,
    mut v___y_3216_: *mut LeanObject,
    mut v___y_3217_: *mut LeanObject,
    mut v___y_3218_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_m_3207_) == 0 {
        let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
        v___x_3220_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0), core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once), _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
        v___x_3221_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v___x_3220_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
        return v___x_3221_;
    } else {
        let mut v_p_3222_: *mut LeanObject = core::ptr::null_mut();
        let mut v_m_3223_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
        v_p_3222_ = lean_ctor_get(v_m_3207_, 0);
        lean_inc_ref(v_p_3222_);
        v_m_3223_ = lean_ctor_get(v_m_3207_, 1);
        lean_inc(v_m_3223_);
        lean_dec_ref_known(v_m_3207_, 2);
        v___x_3224_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__9(v_p_3222_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
        if lean_obj_tag(v___x_3224_) == 0 {
            let mut v_a_3225_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
            v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
            lean_inc(v_a_3225_);
            lean_dec_ref_known(v___x_3224_, 1);
            v___x_3226_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4_spec__10(v_m_3223_, v_a_3225_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
            return v___x_3226_;
        } else {
            lean_dec(v_m_3223_);
            return v___x_3224_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___boxed(
    mut v_m_3227_: *mut LeanObject,
    mut v___y_3228_: *mut LeanObject,
    mut v___y_3229_: *mut LeanObject,
    mut v___y_3230_: *mut LeanObject,
    mut v___y_3231_: *mut LeanObject,
    mut v___y_3232_: *mut LeanObject,
    mut v___y_3233_: *mut LeanObject,
    mut v___y_3234_: *mut LeanObject,
    mut v___y_3235_: *mut LeanObject,
    mut v___y_3236_: *mut LeanObject,
    mut v___y_3237_: *mut LeanObject,
    mut v___y_3238_: *mut LeanObject,
    mut v___y_3239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3240_: *mut LeanObject = core::ptr::null_mut();
    v_res_3240_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_m_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
    lean_dec(v___y_3238_);
    lean_dec_ref(v___y_3237_);
    lean_dec(v___y_3236_);
    lean_dec_ref(v___y_3235_);
    lean_dec(v___y_3234_);
    lean_dec_ref(v___y_3233_);
    lean_dec(v___y_3232_);
    lean_dec_ref(v___y_3231_);
    lean_dec(v___y_3230_);
    lean_dec(v___y_3229_);
    lean_dec_ref(v___y_3228_);
    return v_res_3240_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1(
    mut v_k_3241_: *mut LeanObject,
    mut v_m_3242_: *mut LeanObject,
    mut v___y_3243_: *mut LeanObject,
    mut v___y_3244_: *mut LeanObject,
    mut v___y_3245_: *mut LeanObject,
    mut v___y_3246_: *mut LeanObject,
    mut v___y_3247_: *mut LeanObject,
    mut v___y_3248_: *mut LeanObject,
    mut v___y_3249_: *mut LeanObject,
    mut v___y_3250_: *mut LeanObject,
    mut v___y_3251_: *mut LeanObject,
    mut v___y_3252_: *mut LeanObject,
    mut v___y_3253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: u8 = 0;
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3265_: u8 = 0;
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3270_: u8 = 0;
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3255_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0), core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0_once), _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4___closed__0);
                v___x_3256_ = lean_int_dec_eq(v_k_3241_, v___x_3255_);
                if v___x_3256_ == 0 {
                    v___x_3257_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__3(v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
                    if lean_obj_tag(v___x_3257_) == 0 {
                        v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
                        lean_inc(v_a_3258_);
                        lean_dec_ref_known(v___x_3257_, 1);
                        v___x_3259_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_3241_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
                        if lean_obj_tag(v___x_3259_) == 0 {
                            v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
                            lean_inc(v_a_3260_);
                            lean_dec_ref_known(v___x_3259_, 1);
                            v___x_3261_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1_spec__4(v_m_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
                            if lean_obj_tag(v___x_3261_) == 0 {
                                v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
                                v_isSharedCheck_3270_ = (!lean_is_exclusive(v___x_3261_)) as u8;
                                if v_isSharedCheck_3270_ == 0 {
                                    v___x_3264_ = v___x_3261_;
                                    v_isShared_3265_ = v_isSharedCheck_3270_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_3262_);
                                    lean_dec(v___x_3261_);
                                    v___x_3264_ = lean_box(0);
                                    v_isShared_3265_ = v_isSharedCheck_3270_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3260_);
                                lean_dec(v_a_3258_);
                                return v___x_3261_;
                            }
                        } else {
                            lean_dec(v_a_3258_);
                            lean_dec(v_m_3242_);
                            return v___x_3259_;
                        }
                    } else {
                        lean_dec(v_m_3242_);
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
                    lean_ctor_set(v___x_3264_, 0, v___x_3266_);
                    v___x_3268_ = v___x_3264_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3266_);
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
    mut v_k_3272_: *mut LeanObject,
    mut v_m_3273_: *mut LeanObject,
    mut v___y_3274_: *mut LeanObject,
    mut v___y_3275_: *mut LeanObject,
    mut v___y_3276_: *mut LeanObject,
    mut v___y_3277_: *mut LeanObject,
    mut v___y_3278_: *mut LeanObject,
    mut v___y_3279_: *mut LeanObject,
    mut v___y_3280_: *mut LeanObject,
    mut v___y_3281_: *mut LeanObject,
    mut v___y_3282_: *mut LeanObject,
    mut v___y_3283_: *mut LeanObject,
    mut v___y_3284_: *mut LeanObject,
    mut v___y_3285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3286_: *mut LeanObject = core::ptr::null_mut();
    v_res_3286_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_3272_, v_m_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
    lean_dec(v___y_3284_);
    lean_dec_ref(v___y_3283_);
    lean_dec(v___y_3282_);
    lean_dec_ref(v___y_3281_);
    lean_dec(v___y_3280_);
    lean_dec_ref(v___y_3279_);
    lean_dec(v___y_3278_);
    lean_dec_ref(v___y_3277_);
    lean_dec(v___y_3276_);
    lean_dec(v___y_3275_);
    lean_dec_ref(v___y_3274_);
    lean_dec(v_k_3272_);
    return v_res_3286_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2(
    mut v_p_3287_: *mut LeanObject,
    mut v_acc_3288_: *mut LeanObject,
    mut v___y_3289_: *mut LeanObject,
    mut v___y_3290_: *mut LeanObject,
    mut v___y_3291_: *mut LeanObject,
    mut v___y_3292_: *mut LeanObject,
    mut v___y_3293_: *mut LeanObject,
    mut v___y_3294_: *mut LeanObject,
    mut v___y_3295_: *mut LeanObject,
    mut v___y_3296_: *mut LeanObject,
    mut v___y_3297_: *mut LeanObject,
    mut v___y_3298_: *mut LeanObject,
    mut v___y_3299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3304_: u8 = 0;
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: u8 = 0;
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3318_: u8 = 0;
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3322_: u8 = 0;
    let mut v_k_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_3287_) == 0 {
                    v_k_3301_ = lean_ctor_get(v_p_3287_, 0);
                    v_isSharedCheck_3322_ = (!lean_is_exclusive(v_p_3287_)) as u8;
                    if v_isSharedCheck_3322_ == 0 {
                        v___x_3303_ = v_p_3287_;
                        v_isShared_3304_ = v_isSharedCheck_3322_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_3301_);
                        lean_dec(v_p_3287_);
                        v___x_3303_ = lean_box(0);
                        v_isShared_3304_ = v_isSharedCheck_3322_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_3323_ = lean_ctor_get(v_p_3287_, 0);
                    lean_inc(v_k_3323_);
                    v_v_3324_ = lean_ctor_get(v_p_3287_, 1);
                    lean_inc(v_v_3324_);
                    v_p_3325_ = lean_ctor_get(v_p_3287_, 2);
                    lean_inc_ref(v_p_3325_);
                    lean_dec_ref_known(v_p_3287_, 3);
                    v___x_3326_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
                    if lean_obj_tag(v___x_3326_) == 0 {
                        v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
                        lean_inc(v_a_3327_);
                        lean_dec_ref_known(v___x_3326_, 1);
                        v___x_3328_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_3323_, v_v_3324_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
                        lean_dec(v_k_3323_);
                        if lean_obj_tag(v___x_3328_) == 0 {
                            v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
                            lean_inc(v_a_3329_);
                            lean_dec_ref_known(v___x_3328_, 1);
                            v___x_3330_ = l_Lean_mkAppB(v_a_3327_, v_acc_3288_, v_a_3329_);
                            v_p_3287_ = v_p_3325_;
                            v_acc_3288_ = v___x_3330_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_a_3327_);
                            lean_dec_ref(v_p_3325_);
                            lean_dec_ref(v_acc_3288_);
                            return v___x_3328_;
                        }
                    } else {
                        lean_dec_ref(v_p_3325_);
                        lean_dec(v_v_3324_);
                        lean_dec(v_k_3323_);
                        lean_dec_ref(v_acc_3288_);
                        return v___x_3326_;
                    }
                }
            }
            1 => {
                v___x_3305_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4_once), _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0___closed__4);
                v___x_3306_ = lean_int_dec_eq(v_k_3301_, v___x_3305_);
                if v___x_3306_ == 0 {
                    lean_del_object(v___x_3303_);
                    v___x_3307_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2_spec__6(v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
                    if lean_obj_tag(v___x_3307_) == 0 {
                        v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
                        lean_inc(v_a_3308_);
                        lean_dec_ref_known(v___x_3307_, 1);
                        v___x_3309_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_3301_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
                        lean_dec(v_k_3301_);
                        if lean_obj_tag(v___x_3309_) == 0 {
                            v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
                            v_isSharedCheck_3318_ = (!lean_is_exclusive(v___x_3309_)) as u8;
                            if v_isSharedCheck_3318_ == 0 {
                                v___x_3312_ = v___x_3309_;
                                v_isShared_3313_ = v_isSharedCheck_3318_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_3310_);
                                lean_dec(v___x_3309_);
                                v___x_3312_ = lean_box(0);
                                v_isShared_3313_ = v_isSharedCheck_3318_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3308_);
                            lean_dec_ref(v_acc_3288_);
                            return v___x_3309_;
                        }
                    } else {
                        lean_dec(v_k_3301_);
                        lean_dec_ref(v_acc_3288_);
                        return v___x_3307_;
                    }
                } else {
                    lean_dec(v_k_3301_);
                    if v_isShared_3304_ == 0 {
                        lean_ctor_set(v___x_3303_, 0, v_acc_3288_);
                        v___x_3320_ = v___x_3303_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_acc_3288_);
                        v___x_3320_ = v_reuseFailAlloc_3321_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3314_ = l_Lean_mkAppB(v_a_3308_, v_acc_3288_, v_a_3310_);
                if v_isShared_3313_ == 0 {
                    lean_ctor_set(v___x_3312_, 0, v___x_3314_);
                    v___x_3316_ = v___x_3312_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
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
    mut v_p_3332_: *mut LeanObject,
    mut v_acc_3333_: *mut LeanObject,
    mut v___y_3334_: *mut LeanObject,
    mut v___y_3335_: *mut LeanObject,
    mut v___y_3336_: *mut LeanObject,
    mut v___y_3337_: *mut LeanObject,
    mut v___y_3338_: *mut LeanObject,
    mut v___y_3339_: *mut LeanObject,
    mut v___y_3340_: *mut LeanObject,
    mut v___y_3341_: *mut LeanObject,
    mut v___y_3342_: *mut LeanObject,
    mut v___y_3343_: *mut LeanObject,
    mut v___y_3344_: *mut LeanObject,
    mut v___y_3345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3346_: *mut LeanObject = core::ptr::null_mut();
    v_res_3346_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_3332_, v_acc_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
    lean_dec(v___y_3344_);
    lean_dec_ref(v___y_3343_);
    lean_dec(v___y_3342_);
    lean_dec_ref(v___y_3341_);
    lean_dec(v___y_3340_);
    lean_dec_ref(v___y_3339_);
    lean_dec(v___y_3338_);
    lean_dec_ref(v___y_3337_);
    lean_dec(v___y_3336_);
    lean_dec(v___y_3335_);
    lean_dec_ref(v___y_3334_);
    return v_res_3346_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0(
    mut v_p_3347_: *mut LeanObject,
    mut v___y_3348_: *mut LeanObject,
    mut v___y_3349_: *mut LeanObject,
    mut v___y_3350_: *mut LeanObject,
    mut v___y_3351_: *mut LeanObject,
    mut v___y_3352_: *mut LeanObject,
    mut v___y_3353_: *mut LeanObject,
    mut v___y_3354_: *mut LeanObject,
    mut v___y_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
    mut v___y_3357_: *mut LeanObject,
    mut v___y_3358_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_3347_) == 0 {
        let mut v_k_3360_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
        v_k_3360_ = lean_ctor_get(v_p_3347_, 0);
        lean_inc(v_k_3360_);
        lean_dec_ref_known(v_p_3347_, 1);
        v___x_3361_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0(v_k_3360_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
        lean_dec(v_k_3360_);
        return v___x_3361_;
    } else {
        let mut v_k_3362_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_3363_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_3364_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
        v_k_3362_ = lean_ctor_get(v_p_3347_, 0);
        lean_inc(v_k_3362_);
        v_v_3363_ = lean_ctor_get(v_p_3347_, 1);
        lean_inc(v_v_3363_);
        v_p_3364_ = lean_ctor_get(v_p_3347_, 2);
        lean_inc_ref(v_p_3364_);
        lean_dec_ref_known(v_p_3347_, 3);
        v___x_3365_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__1(v_k_3362_, v_v_3363_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
        lean_dec(v_k_3362_);
        if lean_obj_tag(v___x_3365_) == 0 {
            let mut v_a_3366_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
            v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
            lean_inc(v_a_3366_);
            lean_dec_ref_known(v___x_3365_, 1);
            v___x_3367_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__2(v_p_3364_, v_a_3366_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
            return v___x_3367_;
        } else {
            lean_dec_ref(v_p_3364_);
            return v___x_3365_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0___boxed(
    mut v_p_3368_: *mut LeanObject,
    mut v___y_3369_: *mut LeanObject,
    mut v___y_3370_: *mut LeanObject,
    mut v___y_3371_: *mut LeanObject,
    mut v___y_3372_: *mut LeanObject,
    mut v___y_3373_: *mut LeanObject,
    mut v___y_3374_: *mut LeanObject,
    mut v___y_3375_: *mut LeanObject,
    mut v___y_3376_: *mut LeanObject,
    mut v___y_3377_: *mut LeanObject,
    mut v___y_3378_: *mut LeanObject,
    mut v___y_3379_: *mut LeanObject,
    mut v___y_3380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3381_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3379_);
    lean_dec_ref(v___y_3378_);
    lean_dec(v___y_3377_);
    lean_dec_ref(v___y_3376_);
    lean_dec(v___y_3375_);
    lean_dec_ref(v___y_3374_);
    lean_dec(v___y_3373_);
    lean_dec_ref(v___y_3372_);
    lean_dec(v___y_3371_);
    lean_dec(v___y_3370_);
    lean_dec_ref(v___y_3369_);
    return v_res_3381_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0()
-> f64 {
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: f64 = 0.0;
    v___x_3382_ = lean_unsigned_to_nat(0);
    v___x_3383_ = lean_float_of_nat(v___x_3382_);
    return v___x_3383_;
}
pub unsafe fn l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg(
    mut v_cls_3387_: *mut LeanObject,
    mut v_msg_3388_: *mut LeanObject,
    mut v___y_3389_: *mut LeanObject,
    mut v___y_3390_: *mut LeanObject,
    mut v___y_3391_: *mut LeanObject,
    mut v___y_3392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3399_: u8 = 0;
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3412_: u8 = 0;
    let mut v_tid_3413_: u64 = 0;
    let mut v_traces_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3417_: u8 = 0;
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: f64 = 0.0;
    let mut v___x_3420_: u8 = 0;
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3438_: u8 = 0;
    let mut v_isSharedCheck_3439_: u8 = 0;
    let mut v_isSharedCheck_3440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3394_ = lean_ctor_get(v___y_3391_, 5);
                v___x_3395_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1_spec__4(v_msg_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
                v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
                v_isSharedCheck_3440_ = (!lean_is_exclusive(v___x_3395_)) as u8;
                if v_isSharedCheck_3440_ == 0 {
                    v___x_3398_ = v___x_3395_;
                    v_isShared_3399_ = v_isSharedCheck_3440_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3396_);
                    lean_dec(v___x_3395_);
                    v___x_3398_ = lean_box(0);
                    v_isShared_3399_ = v_isSharedCheck_3440_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3400_ = lean_st_ref_take(v___y_3392_);
                v_traceState_3401_ = lean_ctor_get(v___x_3400_, 4);
                v_env_3402_ = lean_ctor_get(v___x_3400_, 0);
                v_nextMacroScope_3403_ = lean_ctor_get(v___x_3400_, 1);
                v_ngen_3404_ = lean_ctor_get(v___x_3400_, 2);
                v_auxDeclNGen_3405_ = lean_ctor_get(v___x_3400_, 3);
                v_cache_3406_ = lean_ctor_get(v___x_3400_, 5);
                v_messages_3407_ = lean_ctor_get(v___x_3400_, 6);
                v_infoState_3408_ = lean_ctor_get(v___x_3400_, 7);
                v_snapshotTasks_3409_ = lean_ctor_get(v___x_3400_, 8);
                v_isSharedCheck_3439_ = (!lean_is_exclusive(v___x_3400_)) as u8;
                if v_isSharedCheck_3439_ == 0 {
                    v___x_3411_ = v___x_3400_;
                    v_isShared_3412_ = v_isSharedCheck_3439_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3409_);
                    lean_inc(v_infoState_3408_);
                    lean_inc(v_messages_3407_);
                    lean_inc(v_cache_3406_);
                    lean_inc(v_traceState_3401_);
                    lean_inc(v_auxDeclNGen_3405_);
                    lean_inc(v_ngen_3404_);
                    lean_inc(v_nextMacroScope_3403_);
                    lean_inc(v_env_3402_);
                    lean_dec(v___x_3400_);
                    v___x_3411_ = lean_box(0);
                    v_isShared_3412_ = v_isSharedCheck_3439_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3413_ = lean_ctor_get_uint64(
                    v_traceState_3401_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_3414_ = lean_ctor_get(v_traceState_3401_, 0);
                v_isSharedCheck_3438_ = (!lean_is_exclusive(v_traceState_3401_)) as u8;
                if v_isSharedCheck_3438_ == 0 {
                    v___x_3416_ = v_traceState_3401_;
                    v_isShared_3417_ = v_isSharedCheck_3438_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_3414_);
                    lean_dec(v_traceState_3401_);
                    v___x_3416_ = lean_box(0);
                    v_isShared_3417_ = v_isSharedCheck_3438_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3418_ = lean_box(0);
                v___x_3419_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__0);
                v___x_3420_ = 0;
                v___x_3421_ = l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__1;
                v___x_3422_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_3422_, 0, v_cls_3387_);
                lean_ctor_set(v___x_3422_, 1, v___x_3418_);
                lean_ctor_set(v___x_3422_, 2, v___x_3421_);
                lean_ctor_set_float(
                    v___x_3422_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3419_,
                );
                lean_ctor_set_float(
                    v___x_3422_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_3419_,
                );
                lean_ctor_set_uint8(
                    v___x_3422_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_3420_,
                );
                v___x_3423_ = l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg___closed__2;
                v___x_3424_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_3424_, 0, v___x_3422_);
                lean_ctor_set(v___x_3424_, 1, v_a_3396_);
                lean_ctor_set(v___x_3424_, 2, v___x_3423_);
                lean_inc(v_ref_3394_);
                v___x_3425_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3425_, 0, v_ref_3394_);
                lean_ctor_set(v___x_3425_, 1, v___x_3424_);
                v___x_3426_ = l_Lean_PersistentArray_push___redArg(v_traces_3414_, v___x_3425_);
                if v_isShared_3417_ == 0 {
                    lean_ctor_set(v___x_3416_, 0, v___x_3426_);
                    v___x_3428_ = v___x_3416_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3426_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_3437_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_3413_,
                    );
                    v___x_3428_ = v_reuseFailAlloc_3437_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3412_ == 0 {
                    lean_ctor_set(v___x_3411_, 4, v___x_3428_);
                    v___x_3430_ = v___x_3411_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_env_3402_);
                    lean_ctor_set(v_reuseFailAlloc_3436_, 1, v_nextMacroScope_3403_);
                    lean_ctor_set(v_reuseFailAlloc_3436_, 2, v_ngen_3404_);
                    lean_ctor_set(v_reuseFailAlloc_3436_, 3, v_auxDeclNGen_3405_);
                    lean_ctor_set(v_reuseFailAlloc_3436_, 4, v___x_3428_);
                    lean_ctor_set(v_reuseFailAlloc_3436_, 5, v_cache_3406_);
                    lean_ctor_set(v_reuseFailAlloc_3436_, 6, v_messages_3407_);
                    lean_ctor_set(v_reuseFailAlloc_3436_, 7, v_infoState_3408_);
                    lean_ctor_set(v_reuseFailAlloc_3436_, 8, v_snapshotTasks_3409_);
                    v___x_3430_ = v_reuseFailAlloc_3436_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3431_ = lean_st_ref_set(v___y_3392_, v___x_3430_);
                v___x_3432_ = lean_box(0);
                if v_isShared_3399_ == 0 {
                    lean_ctor_set(v___x_3398_, 0, v___x_3432_);
                    v___x_3434_ = v___x_3398_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3432_);
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
    mut v_cls_3441_: *mut LeanObject,
    mut v_msg_3442_: *mut LeanObject,
    mut v___y_3443_: *mut LeanObject,
    mut v___y_3444_: *mut LeanObject,
    mut v___y_3445_: *mut LeanObject,
    mut v___y_3446_: *mut LeanObject,
    mut v___y_3447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3448_: *mut LeanObject = core::ptr::null_mut();
    v_res_3448_ = l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg(
        v_cls_3441_,
        v_msg_3442_,
        v___y_3443_,
        v___y_3444_,
        v___y_3445_,
        v___y_3446_,
    );
    lean_dec(v___y_3446_);
    lean_dec_ref(v___y_3445_);
    lean_dec(v___y_3444_);
    lean_dec_ref(v___y_3443_);
    return v_res_3448_;
}
pub unsafe fn _init_l_Int_Linear_Poly_normCommRing_x3f___closed__0() -> *mut LeanObject {
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    v___x_3449_ = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
    v___x_3450_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3450_, 0, v___x_3449_);
    return v___x_3450_;
}
pub unsafe fn _init_l_Int_Linear_Poly_normCommRing_x3f___closed__8() -> *mut LeanObject {
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    v___x_3463_ = l_Int_Linear_Poly_normCommRing_x3f___closed__5;
    v___x_3464_ = l_Int_Linear_Poly_normCommRing_x3f___closed__7;
    v___x_3465_ = l_Lean_Name_append(v___x_3464_, v___x_3463_);
    return v___x_3465_;
}
pub unsafe fn _init_l_Int_Linear_Poly_normCommRing_x3f___closed__10() -> *mut LeanObject {
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    v___x_3467_ = l_Int_Linear_Poly_normCommRing_x3f___closed__9;
    v___x_3468_ = l_Lean_stringToMessageData(v___x_3467_);
    return v___x_3468_;
}
pub unsafe fn l_Int_Linear_Poly_normCommRing_x3f(
    mut v_p_3469_: *mut LeanObject,
    mut v_a_3470_: *mut LeanObject,
    mut v_a_3471_: *mut LeanObject,
    mut v_a_3472_: *mut LeanObject,
    mut v_a_3473_: *mut LeanObject,
    mut v_a_3474_: *mut LeanObject,
    mut v_a_3475_: *mut LeanObject,
    mut v_a_3476_: *mut LeanObject,
    mut v_a_3477_: *mut LeanObject,
    mut v_a_3478_: *mut LeanObject,
    mut v_a_3479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3485_: u8 = 0;
    let mut v___x_3486_: u8 = 0;
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3495_: u8 = 0;
    let mut v_val_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: u8 = 0;
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: u8 = 0;
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3512_: u8 = 0;
    let mut v_val_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3518_: u8 = 0;
    let mut v_val_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3522_: u8 = 0;
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3531_: u8 = 0;
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3536_: u8 = 0;
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: u8 = 0;
    let mut v___f_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3551_: u8 = 0;
    let mut v_inheritedTraceOptions_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: u8 = 0;
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3567_: u8 = 0;
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3571_: u8 = 0;
    let mut v_a_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3575_: u8 = 0;
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3579_: u8 = 0;
    let mut v_a_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3583_: u8 = 0;
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3587_: u8 = 0;
    let mut v_a_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3591_: u8 = 0;
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3595_: u8 = 0;
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3600_: u8 = 0;
    let mut v_a_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3604_: u8 = 0;
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3608_: u8 = 0;
    let mut v_isSharedCheck_3609_: u8 = 0;
    let mut v_unused_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3614_: u8 = 0;
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3618_: u8 = 0;
    let mut v_a_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3622_: u8 = 0;
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3626_: u8 = 0;
    let mut v_a_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3630_: u8 = 0;
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3634_: u8 = 0;
    let mut v_isSharedCheck_3635_: u8 = 0;
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3640_: u8 = 0;
    let mut v_a_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3644_: u8 = 0;
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3648_: u8 = 0;
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3653_: u8 = 0;
    let mut v_a_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3657_: u8 = 0;
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3661_: u8 = 0;
    let mut v_a_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3665_: u8 = 0;
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3669_: u8 = 0;
    let mut v_a_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3673_: u8 = 0;
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3677_: u8 = 0;
    let mut v_a_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3681_: u8 = 0;
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3685_: u8 = 0;
    let mut v_a_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3689_: u8 = 0;
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3693_: u8 = 0;
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3698_: u8 = 0;
    let mut v_a_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3702_: u8 = 0;
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3706_: u8 = 0;
    let mut v_isSharedCheck_3707_: u8 = 0;
    let mut v_a_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3711_: u8 = 0;
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3715_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3481_ =
                    l_Int_Linear_Poly_isNonlinear___redArg(v_p_3469_, v_a_3470_, v_a_3478_);
                if lean_obj_tag(v___x_3481_) == 0 {
                    v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
                    v_isSharedCheck_3707_ = (!lean_is_exclusive(v___x_3481_)) as u8;
                    if v_isSharedCheck_3707_ == 0 {
                        v___x_3484_ = v___x_3481_;
                        v_isShared_3485_ = v_isSharedCheck_3707_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3482_);
                        lean_dec(v___x_3481_);
                        v___x_3484_ = lean_box(0);
                        v_isShared_3485_ = v_isSharedCheck_3707_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_p_3469_);
                    v_a_3708_ = lean_ctor_get(v___x_3481_, 0);
                    v_isSharedCheck_3715_ = (!lean_is_exclusive(v___x_3481_)) as u8;
                    if v_isSharedCheck_3715_ == 0 {
                        v___x_3710_ = v___x_3481_;
                        v_isShared_3711_ = v_isSharedCheck_3715_;
                        state = 46;
                        continue;
                    } else {
                        lean_inc(v_a_3708_);
                        lean_dec(v___x_3481_);
                        v___x_3710_ = lean_box(0);
                        v_isShared_3711_ = v_isSharedCheck_3715_;
                        state = 46;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3486_ = (lean_unbox(v_a_3482_) as u8);
                if v___x_3486_ == 0 {
                    lean_dec(v_a_3482_);
                    lean_dec_ref(v_p_3469_);
                    v___x_3487_ = lean_box(0);
                    if v_isShared_3485_ == 0 {
                        lean_ctor_set(v___x_3484_, 0, v___x_3487_);
                        v___x_3489_ = v___x_3484_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3487_);
                        v___x_3489_ = v_reuseFailAlloc_3490_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3484_);
                    v___x_3491_ = l_Lean_Meta_Grind_Arith_Cutsat_getIntRingId_x3f(
                        v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_,
                        v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_,
                    );
                    if lean_obj_tag(v___x_3491_) == 0 {
                        v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
                        v_isSharedCheck_3698_ = (!lean_is_exclusive(v___x_3491_)) as u8;
                        if v_isSharedCheck_3698_ == 0 {
                            v___x_3494_ = v___x_3491_;
                            v_isShared_3495_ = v_isSharedCheck_3698_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3492_);
                            lean_dec(v___x_3491_);
                            v___x_3494_ = lean_box(0);
                            v_isShared_3495_ = v_isSharedCheck_3698_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3482_);
                        lean_dec_ref(v_p_3469_);
                        v_a_3699_ = lean_ctor_get(v___x_3491_, 0);
                        v_isSharedCheck_3706_ = (!lean_is_exclusive(v___x_3491_)) as u8;
                        if v_isSharedCheck_3706_ == 0 {
                            v___x_3701_ = v___x_3491_;
                            v_isShared_3702_ = v_isSharedCheck_3706_;
                            state = 44;
                            continue;
                        } else {
                            lean_inc(v_a_3699_);
                            lean_dec(v___x_3491_);
                            v___x_3701_ = lean_box(0);
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
                if lean_obj_tag(v_a_3492_) == 1 {
                    lean_del_object(v___x_3494_);
                    v_val_3496_ = lean_ctor_get(v_a_3492_, 0);
                    lean_inc(v_val_3496_);
                    lean_dec_ref_known(v_a_3492_, 1);
                    lean_inc_ref(v_p_3469_);
                    v___x_3497_ =
                        l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_3469_, v_a_3470_, v_a_3478_);
                    if lean_obj_tag(v___x_3497_) == 0 {
                        v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
                        lean_inc(v_a_3498_);
                        lean_dec_ref_known(v___x_3497_, 1);
                        v___x_3499_ = l_Lean_Meta_Sym_canon(
                            v_a_3498_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_,
                            v_a_3479_,
                        );
                        if lean_obj_tag(v___x_3499_) == 0 {
                            v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
                            lean_inc(v_a_3500_);
                            lean_dec_ref_known(v___x_3499_, 1);
                            v___x_3501_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_3500_, v_a_3475_);
                            if lean_obj_tag(v___x_3501_) == 0 {
                                v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
                                lean_inc(v_a_3502_);
                                lean_dec_ref_known(v___x_3501_, 1);
                                lean_inc_ref(v_p_3469_);
                                v___x_3503_ = l_Int_Linear_Poly_getGeneration___redArg(
                                    v_p_3469_, v_a_3470_, v_a_3478_,
                                );
                                if lean_obj_tag(v___x_3503_) == 0 {
                                    v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
                                    lean_inc_n(v_a_3504_, 2);
                                    lean_dec_ref_known(v___x_3503_, 1);
                                    v___x_3505_ = 0;
                                    v___x_3506_ = lean_alloc_ctor(0, 1, (1) as u32);
                                    lean_ctor_set(v___x_3506_, 0, v_val_3496_);
                                    lean_ctor_set_uint8(
                                        v___x_3506_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                        v___x_3505_,
                                    );
                                    v___x_3507_ = (lean_unbox(v_a_3482_) as u8);
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
                                    if lean_obj_tag(v___x_3508_) == 0 {
                                        v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
                                        v_isSharedCheck_3653_ =
                                            (!lean_is_exclusive(v___x_3508_)) as u8;
                                        if v_isSharedCheck_3653_ == 0 {
                                            v___x_3511_ = v___x_3508_;
                                            v_isShared_3512_ = v_isSharedCheck_3653_;
                                            state = 4;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3509_);
                                            lean_dec(v___x_3508_);
                                            v___x_3511_ = lean_box(0);
                                            v_isShared_3512_ = v_isSharedCheck_3653_;
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref_known(v___x_3506_, 1);
                                        lean_dec(v_a_3504_);
                                        lean_dec(v_a_3482_);
                                        lean_dec_ref(v_p_3469_);
                                        v_a_3654_ = lean_ctor_get(v___x_3508_, 0);
                                        v_isSharedCheck_3661_ =
                                            (!lean_is_exclusive(v___x_3508_)) as u8;
                                        if v_isSharedCheck_3661_ == 0 {
                                            v___x_3656_ = v___x_3508_;
                                            v_isShared_3657_ = v_isSharedCheck_3661_;
                                            state = 33;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3654_);
                                            lean_dec(v___x_3508_);
                                            v___x_3656_ = lean_box(0);
                                            v_isShared_3657_ = v_isSharedCheck_3661_;
                                            state = 33;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_3502_);
                                    lean_dec(v_val_3496_);
                                    lean_dec(v_a_3482_);
                                    lean_dec_ref(v_p_3469_);
                                    v_a_3662_ = lean_ctor_get(v___x_3503_, 0);
                                    v_isSharedCheck_3669_ = (!lean_is_exclusive(v___x_3503_)) as u8;
                                    if v_isSharedCheck_3669_ == 0 {
                                        v___x_3664_ = v___x_3503_;
                                        v_isShared_3665_ = v_isSharedCheck_3669_;
                                        state = 35;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3662_);
                                        lean_dec(v___x_3503_);
                                        v___x_3664_ = lean_box(0);
                                        v_isShared_3665_ = v_isSharedCheck_3669_;
                                        state = 35;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_3496_);
                                lean_dec(v_a_3482_);
                                lean_dec_ref(v_p_3469_);
                                v_a_3670_ = lean_ctor_get(v___x_3501_, 0);
                                v_isSharedCheck_3677_ = (!lean_is_exclusive(v___x_3501_)) as u8;
                                if v_isSharedCheck_3677_ == 0 {
                                    v___x_3672_ = v___x_3501_;
                                    v_isShared_3673_ = v_isSharedCheck_3677_;
                                    state = 37;
                                    continue;
                                } else {
                                    lean_inc(v_a_3670_);
                                    lean_dec(v___x_3501_);
                                    v___x_3672_ = lean_box(0);
                                    v_isShared_3673_ = v_isSharedCheck_3677_;
                                    state = 37;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_val_3496_);
                            lean_dec(v_a_3482_);
                            lean_dec_ref(v_p_3469_);
                            v_a_3678_ = lean_ctor_get(v___x_3499_, 0);
                            v_isSharedCheck_3685_ = (!lean_is_exclusive(v___x_3499_)) as u8;
                            if v_isSharedCheck_3685_ == 0 {
                                v___x_3680_ = v___x_3499_;
                                v_isShared_3681_ = v_isSharedCheck_3685_;
                                state = 39;
                                continue;
                            } else {
                                lean_inc(v_a_3678_);
                                lean_dec(v___x_3499_);
                                v___x_3680_ = lean_box(0);
                                v_isShared_3681_ = v_isSharedCheck_3685_;
                                state = 39;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_3496_);
                        lean_dec(v_a_3482_);
                        lean_dec_ref(v_p_3469_);
                        v_a_3686_ = lean_ctor_get(v___x_3497_, 0);
                        v_isSharedCheck_3693_ = (!lean_is_exclusive(v___x_3497_)) as u8;
                        if v_isSharedCheck_3693_ == 0 {
                            v___x_3688_ = v___x_3497_;
                            v_isShared_3689_ = v_isSharedCheck_3693_;
                            state = 41;
                            continue;
                        } else {
                            lean_inc(v_a_3686_);
                            lean_dec(v___x_3497_);
                            v___x_3688_ = lean_box(0);
                            v_isShared_3689_ = v_isSharedCheck_3693_;
                            state = 41;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3492_);
                    lean_dec(v_a_3482_);
                    lean_dec_ref(v_p_3469_);
                    v___x_3694_ = lean_box(0);
                    if v_isShared_3495_ == 0 {
                        lean_ctor_set(v___x_3494_, 0, v___x_3694_);
                        v___x_3696_ = v___x_3494_;
                        state = 43;
                        continue;
                    } else {
                        v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3694_);
                        v___x_3696_ = v_reuseFailAlloc_3697_;
                        state = 43;
                        continue;
                    }
                }
            }
            4 => {
                if lean_obj_tag(v_a_3509_) == 1 {
                    lean_del_object(v___x_3511_);
                    v_val_3513_ = lean_ctor_get(v_a_3509_, 0);
                    lean_inc_n(v_val_3513_, 2);
                    lean_dec_ref_known(v_a_3509_, 1);
                    v___x_3514_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_val_3513_, v___x_3506_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_);
                    if lean_obj_tag(v___x_3514_) == 0 {
                        v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
                        v_isSharedCheck_3640_ = (!lean_is_exclusive(v___x_3514_)) as u8;
                        if v_isSharedCheck_3640_ == 0 {
                            v___x_3517_ = v___x_3514_;
                            v_isShared_3518_ = v_isSharedCheck_3640_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3515_);
                            lean_dec(v___x_3514_);
                            v___x_3517_ = lean_box(0);
                            v_isShared_3518_ = v_isSharedCheck_3640_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_3513_);
                        lean_dec_ref_known(v___x_3506_, 1);
                        lean_dec(v_a_3504_);
                        lean_dec(v_a_3482_);
                        lean_dec_ref(v_p_3469_);
                        v_a_3641_ = lean_ctor_get(v___x_3514_, 0);
                        v_isSharedCheck_3648_ = (!lean_is_exclusive(v___x_3514_)) as u8;
                        if v_isSharedCheck_3648_ == 0 {
                            v___x_3643_ = v___x_3514_;
                            v_isShared_3644_ = v_isSharedCheck_3648_;
                            state = 30;
                            continue;
                        } else {
                            lean_inc(v_a_3641_);
                            lean_dec(v___x_3514_);
                            v___x_3643_ = lean_box(0);
                            v_isShared_3644_ = v_isSharedCheck_3648_;
                            state = 30;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3509_);
                    lean_dec_ref_known(v___x_3506_, 1);
                    lean_dec(v_a_3504_);
                    lean_dec(v_a_3482_);
                    lean_dec_ref(v_p_3469_);
                    v___x_3649_ = lean_box(0);
                    if v_isShared_3512_ == 0 {
                        lean_ctor_set(v___x_3511_, 0, v___x_3649_);
                        v___x_3651_ = v___x_3511_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3649_);
                        v___x_3651_ = v_reuseFailAlloc_3652_;
                        state = 32;
                        continue;
                    }
                }
            }
            5 => {
                if lean_obj_tag(v_a_3515_) == 1 {
                    lean_del_object(v___x_3517_);
                    v_val_3519_ = lean_ctor_get(v_a_3515_, 0);
                    v_isSharedCheck_3635_ = (!lean_is_exclusive(v_a_3515_)) as u8;
                    if v_isSharedCheck_3635_ == 0 {
                        v___x_3521_ = v_a_3515_;
                        v_isShared_3522_ = v_isSharedCheck_3635_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_val_3519_);
                        lean_dec(v_a_3515_);
                        v___x_3521_ = lean_box(0);
                        v_isShared_3522_ = v_isSharedCheck_3635_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3515_);
                    lean_dec(v_val_3513_);
                    lean_dec_ref_known(v___x_3506_, 1);
                    lean_dec(v_a_3504_);
                    lean_dec(v_a_3482_);
                    lean_dec_ref(v_p_3469_);
                    v___x_3636_ = lean_box(0);
                    if v_isShared_3518_ == 0 {
                        lean_ctor_set(v___x_3517_, 0, v___x_3636_);
                        v___x_3638_ = v___x_3517_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3636_);
                        v___x_3638_ = v_reuseFailAlloc_3639_;
                        state = 29;
                        continue;
                    }
                }
            }
            6 => {
                lean_inc(v_val_3519_);
                v___x_3523_ = l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0(v_val_3519_, v___x_3506_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_);
                lean_dec_ref_known(v___x_3506_, 1);
                if lean_obj_tag(v___x_3523_) == 0 {
                    v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
                    lean_inc(v_a_3524_);
                    lean_dec_ref_known(v___x_3523_, 1);
                    v___x_3525_ = l_Lean_Meta_Grind_preprocessLight___redArg(
                        v_a_3524_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_,
                        v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_,
                    );
                    if lean_obj_tag(v___x_3525_) == 0 {
                        v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
                        lean_inc_n(v_a_3526_, 2);
                        lean_dec_ref_known(v___x_3525_, 1);
                        v___x_3527_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Int_Linear_Poly_normCommRing_x3f___closed__0),
                            core::ptr::addr_of_mut!(
                                l_Int_Linear_Poly_normCommRing_x3f___closed__0_once
                            ),
                            _init_l_Int_Linear_Poly_normCommRing_x3f___closed__0,
                        );
                        lean_inc(v_a_3479_);
                        lean_inc_ref(v_a_3478_);
                        lean_inc(v_a_3477_);
                        lean_inc_ref(v_a_3476_);
                        lean_inc(v_a_3475_);
                        lean_inc_ref(v_a_3474_);
                        lean_inc(v_a_3473_);
                        lean_inc_ref(v_a_3472_);
                        lean_inc(v_a_3471_);
                        lean_inc(v_a_3470_);
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
                        if lean_obj_tag(v___x_3528_) == 0 {
                            v_isSharedCheck_3609_ = (!lean_is_exclusive(v___x_3528_)) as u8;
                            if v_isSharedCheck_3609_ == 0 {
                                v_unused_3610_ = lean_ctor_get(v___x_3528_, 0);
                                lean_dec(v_unused_3610_);
                                v___x_3530_ = v___x_3528_;
                                v_isShared_3531_ = v_isSharedCheck_3609_;
                                state = 7;
                                continue;
                            } else {
                                lean_dec(v___x_3528_);
                                v___x_3530_ = lean_box(0);
                                v_isShared_3531_ = v_isSharedCheck_3609_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3526_);
                            lean_del_object(v___x_3521_);
                            lean_dec(v_val_3519_);
                            lean_dec(v_val_3513_);
                            lean_dec(v_a_3482_);
                            lean_dec_ref(v_p_3469_);
                            v_a_3611_ = lean_ctor_get(v___x_3528_, 0);
                            v_isSharedCheck_3618_ = (!lean_is_exclusive(v___x_3528_)) as u8;
                            if v_isSharedCheck_3618_ == 0 {
                                v___x_3613_ = v___x_3528_;
                                v_isShared_3614_ = v_isSharedCheck_3618_;
                                state = 23;
                                continue;
                            } else {
                                lean_inc(v_a_3611_);
                                lean_dec(v___x_3528_);
                                v___x_3613_ = lean_box(0);
                                v_isShared_3614_ = v_isSharedCheck_3618_;
                                state = 23;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_3521_);
                        lean_dec(v_val_3519_);
                        lean_dec(v_val_3513_);
                        lean_dec(v_a_3504_);
                        lean_dec(v_a_3482_);
                        lean_dec_ref(v_p_3469_);
                        v_a_3619_ = lean_ctor_get(v___x_3525_, 0);
                        v_isSharedCheck_3626_ = (!lean_is_exclusive(v___x_3525_)) as u8;
                        if v_isSharedCheck_3626_ == 0 {
                            v___x_3621_ = v___x_3525_;
                            v_isShared_3622_ = v_isSharedCheck_3626_;
                            state = 25;
                            continue;
                        } else {
                            lean_inc(v_a_3619_);
                            lean_dec(v___x_3525_);
                            v___x_3621_ = lean_box(0);
                            v_isShared_3622_ = v_isSharedCheck_3626_;
                            state = 25;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3521_);
                    lean_dec(v_val_3519_);
                    lean_dec(v_val_3513_);
                    lean_dec(v_a_3504_);
                    lean_dec(v_a_3482_);
                    lean_dec_ref(v_p_3469_);
                    v_a_3627_ = lean_ctor_get(v___x_3523_, 0);
                    v_isSharedCheck_3634_ = (!lean_is_exclusive(v___x_3523_)) as u8;
                    if v_isSharedCheck_3634_ == 0 {
                        v___x_3629_ = v___x_3523_;
                        v_isShared_3630_ = v_isSharedCheck_3634_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_a_3627_);
                        lean_dec(v___x_3523_);
                        v___x_3629_ = lean_box(0);
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
                if lean_obj_tag(v___x_3532_) == 0 {
                    v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
                    v_isSharedCheck_3600_ = (!lean_is_exclusive(v___x_3532_)) as u8;
                    if v_isSharedCheck_3600_ == 0 {
                        v___x_3535_ = v___x_3532_;
                        v_isShared_3536_ = v_isSharedCheck_3600_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3533_);
                        lean_dec(v___x_3532_);
                        v___x_3535_ = lean_box(0);
                        v_isShared_3536_ = v_isSharedCheck_3600_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3530_);
                    lean_del_object(v___x_3521_);
                    lean_dec(v_val_3519_);
                    lean_dec(v_val_3513_);
                    lean_dec(v_a_3482_);
                    lean_dec_ref(v_p_3469_);
                    v_a_3601_ = lean_ctor_get(v___x_3532_, 0);
                    v_isSharedCheck_3608_ = (!lean_is_exclusive(v___x_3532_)) as u8;
                    if v_isSharedCheck_3608_ == 0 {
                        v___x_3603_ = v___x_3532_;
                        v_isShared_3604_ = v_isSharedCheck_3608_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_3601_);
                        lean_dec(v___x_3532_);
                        v___x_3603_ = lean_box(0);
                        v_isShared_3604_ = v_isSharedCheck_3608_;
                        state = 21;
                        continue;
                    }
                }
            }
            8 => {
                v___x_3546_ = l_Int_Linear_instBEqPoly_beq(v_p_3469_, v_a_3533_);
                if v___x_3546_ == 0 {
                    lean_del_object(v___x_3530_);
                    v___f_3547_ = lean_alloc_closure(
                        l_Int_Linear_Poly_normCommRing_x3f___lam__0___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_3547_, 0, v_a_3482_);
                    v___x_3548_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                    v___x_3549_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3548_, v___f_3547_, v_a_3470_);
                    if lean_obj_tag(v___x_3549_) == 0 {
                        lean_dec_ref_known(v___x_3549_, 1);
                        v_options_3550_ = lean_ctor_get(v_a_3478_, 2);
                        v_hasTrace_3551_ = lean_ctor_get_uint8(
                            v_options_3550_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_3551_ == 0 {
                            lean_dec_ref(v_p_3469_);
                            state = 9;
                            continue;
                        } else {
                            v_inheritedTraceOptions_3552_ = lean_ctor_get(v_a_3478_, 13);
                            v___x_3553_ = l_Int_Linear_Poly_normCommRing_x3f___closed__5;
                            v___x_3554_ = lean_obj_once(
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
                                lean_dec_ref(v_p_3469_);
                                state = 9;
                                continue;
                            } else {
                                v___x_3556_ =
                                    l_Int_Linear_Poly_pp___redArg(v_p_3469_, v_a_3470_, v_a_3478_);
                                if lean_obj_tag(v___x_3556_) == 0 {
                                    v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
                                    lean_inc(v_a_3557_);
                                    lean_dec_ref_known(v___x_3556_, 1);
                                    lean_inc(v_a_3533_);
                                    v___x_3558_ = l_Int_Linear_Poly_pp___redArg(
                                        v_a_3533_, v_a_3470_, v_a_3478_,
                                    );
                                    if lean_obj_tag(v___x_3558_) == 0 {
                                        v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
                                        lean_inc(v_a_3559_);
                                        lean_dec_ref_known(v___x_3558_, 1);
                                        v___x_3560_ = lean_obj_once(core::ptr::addr_of_mut!(l_Int_Linear_Poly_normCommRing_x3f___closed__10), core::ptr::addr_of_mut!(l_Int_Linear_Poly_normCommRing_x3f___closed__10_once), _init_l_Int_Linear_Poly_normCommRing_x3f___closed__10);
                                        v___x_3561_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_3561_, 0, v_a_3557_);
                                        lean_ctor_set(v___x_3561_, 1, v___x_3560_);
                                        v___x_3562_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_3562_, 0, v___x_3561_);
                                        lean_ctor_set(v___x_3562_, 1, v_a_3559_);
                                        v___x_3563_ = l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1___redArg(v___x_3553_, v___x_3562_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_);
                                        if lean_obj_tag(v___x_3563_) == 0 {
                                            lean_dec_ref_known(v___x_3563_, 1);
                                            state = 9;
                                            continue;
                                        } else {
                                            lean_del_object(v___x_3535_);
                                            lean_dec(v_a_3533_);
                                            lean_del_object(v___x_3521_);
                                            lean_dec(v_val_3519_);
                                            lean_dec(v_val_3513_);
                                            v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
                                            v_isSharedCheck_3571_ =
                                                (!lean_is_exclusive(v___x_3563_)) as u8;
                                            if v_isSharedCheck_3571_ == 0 {
                                                v___x_3566_ = v___x_3563_;
                                                v_isShared_3567_ = v_isSharedCheck_3571_;
                                                state = 12;
                                                continue;
                                            } else {
                                                lean_inc(v_a_3564_);
                                                lean_dec(v___x_3563_);
                                                v___x_3566_ = lean_box(0);
                                                v_isShared_3567_ = v_isSharedCheck_3571_;
                                                state = 12;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_3557_);
                                        lean_del_object(v___x_3535_);
                                        lean_dec(v_a_3533_);
                                        lean_del_object(v___x_3521_);
                                        lean_dec(v_val_3519_);
                                        lean_dec(v_val_3513_);
                                        v_a_3572_ = lean_ctor_get(v___x_3558_, 0);
                                        v_isSharedCheck_3579_ =
                                            (!lean_is_exclusive(v___x_3558_)) as u8;
                                        if v_isSharedCheck_3579_ == 0 {
                                            v___x_3574_ = v___x_3558_;
                                            v_isShared_3575_ = v_isSharedCheck_3579_;
                                            state = 14;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3572_);
                                            lean_dec(v___x_3558_);
                                            v___x_3574_ = lean_box(0);
                                            v_isShared_3575_ = v_isSharedCheck_3579_;
                                            state = 14;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_del_object(v___x_3535_);
                                    lean_dec(v_a_3533_);
                                    lean_del_object(v___x_3521_);
                                    lean_dec(v_val_3519_);
                                    lean_dec(v_val_3513_);
                                    v_a_3580_ = lean_ctor_get(v___x_3556_, 0);
                                    v_isSharedCheck_3587_ = (!lean_is_exclusive(v___x_3556_)) as u8;
                                    if v_isSharedCheck_3587_ == 0 {
                                        v___x_3582_ = v___x_3556_;
                                        v_isShared_3583_ = v_isSharedCheck_3587_;
                                        state = 16;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3580_);
                                        lean_dec(v___x_3556_);
                                        v___x_3582_ = lean_box(0);
                                        v_isShared_3583_ = v_isSharedCheck_3587_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_3535_);
                        lean_dec(v_a_3533_);
                        lean_del_object(v___x_3521_);
                        lean_dec(v_val_3519_);
                        lean_dec(v_val_3513_);
                        lean_dec_ref(v_p_3469_);
                        v_a_3588_ = lean_ctor_get(v___x_3549_, 0);
                        v_isSharedCheck_3595_ = (!lean_is_exclusive(v___x_3549_)) as u8;
                        if v_isSharedCheck_3595_ == 0 {
                            v___x_3590_ = v___x_3549_;
                            v_isShared_3591_ = v_isSharedCheck_3595_;
                            state = 18;
                            continue;
                        } else {
                            lean_inc(v_a_3588_);
                            lean_dec(v___x_3549_);
                            v___x_3590_ = lean_box(0);
                            v_isShared_3591_ = v_isSharedCheck_3595_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3535_);
                    lean_dec(v_a_3533_);
                    lean_del_object(v___x_3521_);
                    lean_dec(v_val_3519_);
                    lean_dec(v_val_3513_);
                    lean_dec(v_a_3482_);
                    lean_dec_ref(v_p_3469_);
                    v___x_3596_ = lean_box(0);
                    if v_isShared_3531_ == 0 {
                        lean_ctor_set(v___x_3530_, 0, v___x_3596_);
                        v___x_3598_ = v___x_3530_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3596_);
                        v___x_3598_ = v_reuseFailAlloc_3599_;
                        state = 20;
                        continue;
                    }
                }
            }
            9 => {
                v___x_3538_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3538_, 0, v_val_3519_);
                lean_ctor_set(v___x_3538_, 1, v_a_3533_);
                v___x_3539_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3539_, 0, v_val_3513_);
                lean_ctor_set(v___x_3539_, 1, v___x_3538_);
                if v_isShared_3522_ == 0 {
                    lean_ctor_set(v___x_3521_, 0, v___x_3539_);
                    v___x_3541_ = v___x_3521_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3539_);
                    v___x_3541_ = v_reuseFailAlloc_3545_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_3536_ == 0 {
                    lean_ctor_set(v___x_3535_, 0, v___x_3541_);
                    v___x_3543_ = v___x_3535_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3541_);
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
                    v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3564_);
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
                    v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3572_);
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
                    v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
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
                    v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
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
                    v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
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
                    v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
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
                    v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
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
                    v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
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
                    v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
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
                    v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
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
                    v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3662_);
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
                    v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
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
                    v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
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
                    v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
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
                    v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
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
                    v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
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
    mut v_p_3716_: *mut LeanObject,
    mut v_a_3717_: *mut LeanObject,
    mut v_a_3718_: *mut LeanObject,
    mut v_a_3719_: *mut LeanObject,
    mut v_a_3720_: *mut LeanObject,
    mut v_a_3721_: *mut LeanObject,
    mut v_a_3722_: *mut LeanObject,
    mut v_a_3723_: *mut LeanObject,
    mut v_a_3724_: *mut LeanObject,
    mut v_a_3725_: *mut LeanObject,
    mut v_a_3726_: *mut LeanObject,
    mut v_a_3727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3728_: *mut LeanObject = core::ptr::null_mut();
    v_res_3728_ = l_Int_Linear_Poly_normCommRing_x3f(
        v_p_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_,
        v_a_3724_, v_a_3725_, v_a_3726_,
    );
    lean_dec(v_a_3726_);
    lean_dec_ref(v_a_3725_);
    lean_dec(v_a_3724_);
    lean_dec_ref(v_a_3723_);
    lean_dec(v_a_3722_);
    lean_dec_ref(v_a_3721_);
    lean_dec(v_a_3720_);
    lean_dec_ref(v_a_3719_);
    lean_dec(v_a_3718_);
    lean_dec(v_a_3717_);
    return v_res_3728_;
}
pub unsafe fn l_Lean_addTrace___at___00Int_Linear_Poly_normCommRing_x3f_spec__1(
    mut v_cls_3729_: *mut LeanObject,
    mut v_msg_3730_: *mut LeanObject,
    mut v___y_3731_: *mut LeanObject,
    mut v___y_3732_: *mut LeanObject,
    mut v___y_3733_: *mut LeanObject,
    mut v___y_3734_: *mut LeanObject,
    mut v___y_3735_: *mut LeanObject,
    mut v___y_3736_: *mut LeanObject,
    mut v___y_3737_: *mut LeanObject,
    mut v___y_3738_: *mut LeanObject,
    mut v___y_3739_: *mut LeanObject,
    mut v___y_3740_: *mut LeanObject,
    mut v___y_3741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_cls_3744_: *mut LeanObject,
    mut v_msg_3745_: *mut LeanObject,
    mut v___y_3746_: *mut LeanObject,
    mut v___y_3747_: *mut LeanObject,
    mut v___y_3748_: *mut LeanObject,
    mut v___y_3749_: *mut LeanObject,
    mut v___y_3750_: *mut LeanObject,
    mut v___y_3751_: *mut LeanObject,
    mut v___y_3752_: *mut LeanObject,
    mut v___y_3753_: *mut LeanObject,
    mut v___y_3754_: *mut LeanObject,
    mut v___y_3755_: *mut LeanObject,
    mut v___y_3756_: *mut LeanObject,
    mut v___y_3757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3758_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3756_);
    lean_dec_ref(v___y_3755_);
    lean_dec(v___y_3754_);
    lean_dec_ref(v___y_3753_);
    lean_dec(v___y_3752_);
    lean_dec_ref(v___y_3751_);
    lean_dec(v___y_3750_);
    lean_dec_ref(v___y_3749_);
    lean_dec(v___y_3748_);
    lean_dec(v___y_3747_);
    lean_dec_ref(v___y_3746_);
    return v_res_3758_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(
    mut v_00_u03b1_3759_: *mut LeanObject,
    mut v_msg_3760_: *mut LeanObject,
    mut v___y_3761_: *mut LeanObject,
    mut v___y_3762_: *mut LeanObject,
    mut v___y_3763_: *mut LeanObject,
    mut v___y_3764_: *mut LeanObject,
    mut v___y_3765_: *mut LeanObject,
    mut v___y_3766_: *mut LeanObject,
    mut v___y_3767_: *mut LeanObject,
    mut v___y_3768_: *mut LeanObject,
    mut v___y_3769_: *mut LeanObject,
    mut v___y_3770_: *mut LeanObject,
    mut v___y_3771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    v___x_3773_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_msg_3760_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
    return v___x_3773_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___boxed(
    mut v_00_u03b1_3774_: *mut LeanObject,
    mut v_msg_3775_: *mut LeanObject,
    mut v___y_3776_: *mut LeanObject,
    mut v___y_3777_: *mut LeanObject,
    mut v___y_3778_: *mut LeanObject,
    mut v___y_3779_: *mut LeanObject,
    mut v___y_3780_: *mut LeanObject,
    mut v___y_3781_: *mut LeanObject,
    mut v___y_3782_: *mut LeanObject,
    mut v___y_3783_: *mut LeanObject,
    mut v___y_3784_: *mut LeanObject,
    mut v___y_3785_: *mut LeanObject,
    mut v___y_3786_: *mut LeanObject,
    mut v___y_3787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3788_: *mut LeanObject = core::ptr::null_mut();
    v_res_3788_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Int_Linear_Poly_normCommRing_x3f_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(v_00_u03b1_3774_, v_msg_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
    lean_dec(v___y_3786_);
    lean_dec_ref(v___y_3785_);
    lean_dec(v___y_3784_);
    lean_dec_ref(v___y_3783_);
    lean_dec(v___y_3782_);
    lean_dec_ref(v___y_3781_);
    lean_dec(v___y_3780_);
    lean_dec_ref(v___y_3779_);
    lean_dec(v___y_3778_);
    lean_dec(v___y_3777_);
    lean_dec_ref(v___y_3776_);
    return v_res_3788_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
}
