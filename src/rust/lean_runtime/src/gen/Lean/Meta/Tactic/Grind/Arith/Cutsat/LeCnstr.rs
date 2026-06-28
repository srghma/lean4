// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt Init.Data.Int.OfNat Lean.Meta.Tactic.Simp.Arith.Int Lean.Meta.Tactic.Grind.Arith.Cutsat.Var Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing
use crate::r#gen::Init::Data::Int::Linear::{
    l_Int_Linear_Expr_norm, l_Int_Linear_Poly_addConst, l_Int_Linear_Poly_coeff,
    l_Int_Linear_Poly_combine, l_Int_Linear_Poly_div, l_Int_Linear_Poly_isUnsatLe,
    l_Int_Linear_Poly_mul, l_Int_Linear_Poly_norm, l_Int_Linear_instBEqPoly_beq,
};
use crate::r#gen::Init::Data::Int::OfNat::{
    initialize_Init_Data_Int_OfNat, runtime_initialize_Init_Data_Int_OfNat,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_maxRecDepthErrorMessage,
};
use crate::r#gen::Lean::Data::LBool::l_Lean_instBEqLBool_beq;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_get_x21___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_instInhabitedPersistentArray_default, l_Lean_instInhabitedPersistentArrayNode_default,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf, l_Lean_mkApp6, l_Lean_mkConst, l_Lean_mkIntAdd, l_Lean_mkIntLit,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_instantiateMVarsIfMVarApp___redArg;
use crate::r#gen::Lean::Meta::IntInstTesters::l_Lean_Meta_Structural_isInstLEInt___redArg;
use crate::r#gen::Lean::Meta::LitValues::l_Lean_Meta_getIntValue_x3f;
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getConfig___redArg, l_Lean_Meta_Sym_reportIssue,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::CommRing::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing, l_Int_Linear_Poly_normCommRing_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Nat::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat, l_Lean_Meta_Grind_Arith_Cutsat_natToInt,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Norm::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm,
    l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Proof::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof,
    l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::ToInt::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt,
    l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run, l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg, l_Lean_Meta_Grind_Arith_Cutsat_toInt,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Types::l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Util::{
    l_Int_Linear_Poly_findVarToSubst___redArg, l_Int_Linear_Poly_isSorted,
    l_Int_Linear_Poly_updateOccs___redArg, l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial,
    l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Var::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var, l_Lean_Meta_Grind_Arith_Cutsat_toPoly,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_getConfig___redArg, l_Lean_Meta_Grind_getGeneration___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Arith::Int::Simp::l_Int_Linear_Poly_gcdCoeffs_x27;
use crate::r#gen::Lean::Meta::Tactic::Simp::Arith::Int::{
    initialize_Lean_Meta_Tactic_Simp_Arith_Int, runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_neg, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_borrowed, lean_array_get_size,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Arith::Cutsat::Util::{
    lean_grind_cutsat_assert_eq, lean_grind_cutsat_assert_le,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_13, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64,
    lean_ctor_get_usize, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value: LeanStringObject<6> =
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value: LeanStringObject<4> =
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__2_value: LeanStringObject<6> =
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
        m_data: [115, 117, 98, 115, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__2_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value)
                as *mut LeanObject,
            15947788021050471391 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value)
                as *mut LeanObject,
            11074150007773075224 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__2_value)
                as *mut LeanObject,
            4195518777998369870 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__4_value: LeanStringObject<6> =
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__4_value)
                as *mut LeanObject,
            14231257465488249300 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__7_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [44, 32, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__0_value) as *mut LeanObject,7310567555909517314 as *mut LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__1_value) as *mut LeanObject,273128857561458264 as *mut LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__0_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__3_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [101, 113, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__3_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__2_value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value) as *mut LeanObject,12441483040187581015 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__3_value) as *mut LeanObject,16364433383833919382 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [110, 101, 119, 32, 101, 113, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__0_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__0_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0_value: LeanStringObject<
    7,
> = LeanStringObject {
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__1_value: LeanStringObject<
    6,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [115, 116, 111, 114, 101, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value)
            as *mut LeanObject,
        15947788021050471391 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value)
            as *mut LeanObject,
        11074150007773075224 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0_value)
            as *mut LeanObject,
        10199653630302390726 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__1_value)
                as *mut LeanObject,
            10228816052197840364 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4_value: LeanStringObject<
    8,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [116, 114, 105, 118, 105, 97, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value)
            as *mut LeanObject,
        15947788021050471391 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value)
            as *mut LeanObject,
        11074150007773075224 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0_value)
            as *mut LeanObject,
        10199653630302390726 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4_value)
                as *mut LeanObject,
            16175042957003990705 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7_value: LeanStringObject<
    6,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [117, 110, 115, 97, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value)
            as *mut LeanObject,
        15947788021050471391 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value)
            as *mut LeanObject,
        11074150007773075224 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0_value)
            as *mut LeanObject,
        10199653630302390726 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7_value)
                as *mut LeanObject,
            5443962459141360856 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value)
            as *mut LeanObject,
        15947788021050471391 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value)
            as *mut LeanObject,
        11074150007773075224 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0_value)
                as *mut LeanObject,
            10199653630302390726 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 111, 110, 32, 110, 111, 114, 109, 97, 108, 105, 122, 101, 100, 32, 105, 110, 101, 113, 117, 97, 108, 105, 116, 121, 32, 99, 111, 110, 115, 116, 114, 97, 105, 110, 116, 32, 102, 111, 117, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 69, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__1_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__0_value) as *mut LeanObject,8347582161988589016 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__1_value) as *mut LeanObject,7316284823769321069 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__1_value: LeanStringObject<4> =
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
        m_data: [78, 97, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__2_value: LeanStringObject<6> =
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
        m_data: [84, 111, 73, 110, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__3_value: LeanStringObject<10> =
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
        m_data: [111, 102, 95, 110, 111, 116, 95, 108, 101, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__1_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__2_value)
                as *mut LeanObject,
            16002102443310951684 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__3_value)
                as *mut LeanObject,
            6726769673471554383 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__6_value: LeanStringObject<6> =
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
        m_data: [111, 102, 95, 108, 101, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__6_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__1_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__2_value)
                as *mut LeanObject,
            16002102443310951684 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__6_value)
                as *mut LeanObject,
            17058721431237534825 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__1_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1_value: LeanStringObject<4> =
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
        m_data: [73, 110, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__1_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__0_value)
                as *mut LeanObject,
            17878876274162330439 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__1_value)
                as *mut LeanObject,
            11833570877100518198 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2_value)
        as *mut LeanObject;
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm_spec__0(
    mut v_a_4259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    v___x_4260_ = lean_nat_to_int(v_a_4259_);
    return v___x_4260_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(
    mut v_c_4261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: u8 = 0;
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: u8 = 0;
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_4272_ = lean_ctor_get(v_c_4261_, 0);
                v___x_4273_ = l_Int_Linear_Poly_isSorted(v_p_4272_);
                if v___x_4273_ == 0 {
                    lean_inc_ref(v_p_4272_);
                    v___x_4274_ = l_Int_Linear_Poly_norm(v_p_4272_);
                    v___x_4275_ = lean_alloc_ctor(6, 1, (0) as u32);
                    lean_ctor_set(v___x_4275_, 0, v_c_4261_);
                    lean_inc_ref(v___x_4274_);
                    v___x_4276_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4276_, 0, v___x_4274_);
                    lean_ctor_set(v___x_4276_, 1, v___x_4275_);
                    v___y_4263_ = v___x_4276_;
                    v_p_4264_ = v___x_4274_;
                    state = 1;
                    continue;
                } else {
                    lean_inc_ref(v_p_4272_);
                    v___y_4263_ = v_c_4261_;
                    v_p_4264_ = v_p_4272_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_k_4265_ = l_Int_Linear_Poly_gcdCoeffs_x27(v_p_4264_);
                v___x_4266_ = lean_unsigned_to_nat(1);
                v___x_4267_ = lean_nat_dec_eq(v_k_4265_, v___x_4266_);
                if v___x_4267_ == 0 {
                    v___x_4268_ = lean_nat_to_int(v_k_4265_);
                    v___x_4269_ = l_Int_Linear_Poly_div(v___x_4268_, v_p_4264_);
                    lean_dec(v___x_4268_);
                    v___x_4270_ = lean_alloc_ctor(7, 1, (0) as u32);
                    lean_ctor_set(v___x_4270_, 0, v___y_4263_);
                    v___x_4271_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4271_, 0, v___x_4269_);
                    lean_ctor_set(v___x_4271_, 1, v___x_4270_);
                    return v___x_4271_;
                } else {
                    lean_dec(v_k_4265_);
                    lean_dec_ref(v_p_4264_);
                    return v___y_4263_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(
    mut v_msgData_4277_: *mut LeanObject,
    mut v___y_4278_: *mut LeanObject,
    mut v___y_4279_: *mut LeanObject,
    mut v___y_4280_: *mut LeanObject,
    mut v___y_4281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    v___x_4283_ = lean_st_ref_get(v___y_4281_);
    v_env_4284_ = lean_ctor_get(v___x_4283_, 0);
    lean_inc_ref(v_env_4284_);
    lean_dec(v___x_4283_);
    v___x_4285_ = lean_st_ref_get(v___y_4279_);
    v_mctx_4286_ = lean_ctor_get(v___x_4285_, 0);
    lean_inc_ref(v_mctx_4286_);
    lean_dec(v___x_4285_);
    v_lctx_4287_ = lean_ctor_get(v___y_4278_, 2);
    v_options_4288_ = lean_ctor_get(v___y_4280_, 2);
    lean_inc_ref(v_options_4288_);
    lean_inc_ref(v_lctx_4287_);
    v___x_4289_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4289_, 0, v_env_4284_);
    lean_ctor_set(v___x_4289_, 1, v_mctx_4286_);
    lean_ctor_set(v___x_4289_, 2, v_lctx_4287_);
    lean_ctor_set(v___x_4289_, 3, v_options_4288_);
    v___x_4290_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4290_, 0, v___x_4289_);
    lean_ctor_set(v___x_4290_, 1, v_msgData_4277_);
    v___x_4291_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4291_, 0, v___x_4290_);
    return v___x_4291_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0___boxed(
    mut v_msgData_4292_: *mut LeanObject,
    mut v___y_4293_: *mut LeanObject,
    mut v___y_4294_: *mut LeanObject,
    mut v___y_4295_: *mut LeanObject,
    mut v___y_4296_: *mut LeanObject,
    mut v___y_4297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4298_: *mut LeanObject = core::ptr::null_mut();
    v_res_4298_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(v_msgData_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
    lean_dec(v___y_4296_);
    lean_dec_ref(v___y_4295_);
    lean_dec(v___y_4294_);
    lean_dec_ref(v___y_4293_);
    return v_res_4298_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: f64 = 0.0;
    v___x_4299_ = lean_unsigned_to_nat(0);
    v___x_4300_ = lean_float_of_nat(v___x_4299_);
    return v___x_4300_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(
    mut v_cls_4304_: *mut LeanObject,
    mut v_msg_4305_: *mut LeanObject,
    mut v___y_4306_: *mut LeanObject,
    mut v___y_4307_: *mut LeanObject,
    mut v___y_4308_: *mut LeanObject,
    mut v___y_4309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4329_: u8 = 0;
    let mut v_tid_4330_: u64 = 0;
    let mut v_traces_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4334_: u8 = 0;
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: f64 = 0.0;
    let mut v___x_4337_: u8 = 0;
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4355_: u8 = 0;
    let mut v_isSharedCheck_4356_: u8 = 0;
    let mut v_isSharedCheck_4357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4311_ = lean_ctor_get(v___y_4308_, 5);
                v___x_4312_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(v_msg_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
                v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
                v_isSharedCheck_4357_ = (!lean_is_exclusive(v___x_4312_)) as u8;
                if v_isSharedCheck_4357_ == 0 {
                    v___x_4315_ = v___x_4312_;
                    v_isShared_4316_ = v_isSharedCheck_4357_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4313_);
                    lean_dec(v___x_4312_);
                    v___x_4315_ = lean_box(0);
                    v_isShared_4316_ = v_isSharedCheck_4357_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4317_ = lean_st_ref_take(v___y_4309_);
                v_traceState_4318_ = lean_ctor_get(v___x_4317_, 4);
                v_env_4319_ = lean_ctor_get(v___x_4317_, 0);
                v_nextMacroScope_4320_ = lean_ctor_get(v___x_4317_, 1);
                v_ngen_4321_ = lean_ctor_get(v___x_4317_, 2);
                v_auxDeclNGen_4322_ = lean_ctor_get(v___x_4317_, 3);
                v_cache_4323_ = lean_ctor_get(v___x_4317_, 5);
                v_messages_4324_ = lean_ctor_get(v___x_4317_, 6);
                v_infoState_4325_ = lean_ctor_get(v___x_4317_, 7);
                v_snapshotTasks_4326_ = lean_ctor_get(v___x_4317_, 8);
                v_isSharedCheck_4356_ = (!lean_is_exclusive(v___x_4317_)) as u8;
                if v_isSharedCheck_4356_ == 0 {
                    v___x_4328_ = v___x_4317_;
                    v_isShared_4329_ = v_isSharedCheck_4356_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4326_);
                    lean_inc(v_infoState_4325_);
                    lean_inc(v_messages_4324_);
                    lean_inc(v_cache_4323_);
                    lean_inc(v_traceState_4318_);
                    lean_inc(v_auxDeclNGen_4322_);
                    lean_inc(v_ngen_4321_);
                    lean_inc(v_nextMacroScope_4320_);
                    lean_inc(v_env_4319_);
                    lean_dec(v___x_4317_);
                    v___x_4328_ = lean_box(0);
                    v_isShared_4329_ = v_isSharedCheck_4356_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4330_ = lean_ctor_get_uint64(
                    v_traceState_4318_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_4331_ = lean_ctor_get(v_traceState_4318_, 0);
                v_isSharedCheck_4355_ = (!lean_is_exclusive(v_traceState_4318_)) as u8;
                if v_isSharedCheck_4355_ == 0 {
                    v___x_4333_ = v_traceState_4318_;
                    v_isShared_4334_ = v_isSharedCheck_4355_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_4331_);
                    lean_dec(v_traceState_4318_);
                    v___x_4333_ = lean_box(0);
                    v_isShared_4334_ = v_isSharedCheck_4355_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4335_ = lean_box(0);
                v___x_4336_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0);
                v___x_4337_ = 0;
                v___x_4338_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__1;
                v___x_4339_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_4339_, 0, v_cls_4304_);
                lean_ctor_set(v___x_4339_, 1, v___x_4335_);
                lean_ctor_set(v___x_4339_, 2, v___x_4338_);
                lean_ctor_set_float(
                    v___x_4339_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4336_,
                );
                lean_ctor_set_float(
                    v___x_4339_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_4336_,
                );
                lean_ctor_set_uint8(
                    v___x_4339_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_4337_,
                );
                v___x_4340_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__2;
                v___x_4341_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_4341_, 0, v___x_4339_);
                lean_ctor_set(v___x_4341_, 1, v_a_4313_);
                lean_ctor_set(v___x_4341_, 2, v___x_4340_);
                lean_inc(v_ref_4311_);
                v___x_4342_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4342_, 0, v_ref_4311_);
                lean_ctor_set(v___x_4342_, 1, v___x_4341_);
                v___x_4343_ = l_Lean_PersistentArray_push___redArg(v_traces_4331_, v___x_4342_);
                if v_isShared_4334_ == 0 {
                    lean_ctor_set(v___x_4333_, 0, v___x_4343_);
                    v___x_4345_ = v___x_4333_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4354_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4354_, 0, v___x_4343_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4354_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4330_,
                    );
                    v___x_4345_ = v_reuseFailAlloc_4354_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4329_ == 0 {
                    lean_ctor_set(v___x_4328_, 4, v___x_4345_);
                    v___x_4347_ = v___x_4328_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_env_4319_);
                    lean_ctor_set(v_reuseFailAlloc_4353_, 1, v_nextMacroScope_4320_);
                    lean_ctor_set(v_reuseFailAlloc_4353_, 2, v_ngen_4321_);
                    lean_ctor_set(v_reuseFailAlloc_4353_, 3, v_auxDeclNGen_4322_);
                    lean_ctor_set(v_reuseFailAlloc_4353_, 4, v___x_4345_);
                    lean_ctor_set(v_reuseFailAlloc_4353_, 5, v_cache_4323_);
                    lean_ctor_set(v_reuseFailAlloc_4353_, 6, v_messages_4324_);
                    lean_ctor_set(v_reuseFailAlloc_4353_, 7, v_infoState_4325_);
                    lean_ctor_set(v_reuseFailAlloc_4353_, 8, v_snapshotTasks_4326_);
                    v___x_4347_ = v_reuseFailAlloc_4353_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4348_ = lean_st_ref_set(v___y_4309_, v___x_4347_);
                v___x_4349_ = lean_box(0);
                if v_isShared_4316_ == 0 {
                    lean_ctor_set(v___x_4315_, 0, v___x_4349_);
                    v___x_4351_ = v___x_4315_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___x_4349_);
                    v___x_4351_ = v_reuseFailAlloc_4352_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4351_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___boxed(
    mut v_cls_4358_: *mut LeanObject,
    mut v_msg_4359_: *mut LeanObject,
    mut v___y_4360_: *mut LeanObject,
    mut v___y_4361_: *mut LeanObject,
    mut v___y_4362_: *mut LeanObject,
    mut v___y_4363_: *mut LeanObject,
    mut v___y_4364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4365_: *mut LeanObject = core::ptr::null_mut();
    v_res_4365_ =
        l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(
            v_cls_4358_,
            v_msg_4359_,
            v___y_4360_,
            v___y_4361_,
            v___y_4362_,
            v___y_4363_,
        );
    lean_dec(v___y_4363_);
    lean_dec_ref(v___y_4362_);
    lean_dec(v___y_4361_);
    lean_dec_ref(v___y_4360_);
    return v_res_4365_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6() -> *mut LeanObject
{
    let mut v_cls_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    v_cls_4376_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3;
    v___x_4377_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5;
    v___x_4378_ = l_Lean_Name_append(v___x_4377_, v_cls_4376_);
    return v___x_4378_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8() -> *mut LeanObject
{
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    v___x_4380_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__7;
    v___x_4381_ = l_Lean_stringToMessageData(v___x_4380_);
    return v___x_4381_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9() -> *mut LeanObject
{
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    v___x_4382_ = lean_unsigned_to_nat(0);
    v___x_4383_ = lean_nat_to_int(v___x_4382_);
    return v___x_4383_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(
    mut v_a_4384_: *mut LeanObject,
    mut v_x_4385_: *mut LeanObject,
    mut v_c_u2081_4386_: *mut LeanObject,
    mut v_b_4387_: *mut LeanObject,
    mut v_c_u2082_4388_: *mut LeanObject,
    mut v_a_4389_: *mut LeanObject,
    mut v_a_4390_: *mut LeanObject,
    mut v_a_4391_: *mut LeanObject,
    mut v_a_4392_: *mut LeanObject,
    mut v_a_4393_: *mut LeanObject,
    mut v_a_4394_: *mut LeanObject,
    mut v_a_4395_: *mut LeanObject,
    mut v_a_4396_: *mut LeanObject,
    mut v_a_4397_: *mut LeanObject,
    mut v_a_4398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4408_: u8 = 0;
    let mut v_inheritedTraceOptions_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cls_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: u8 = 0;
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4429_: u8 = 0;
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4433_: u8 = 0;
    let mut v_a_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4437_: u8 = 0;
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4441_: u8 = 0;
    let mut v_a_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4445_: u8 = 0;
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4449_: u8 = 0;
    let mut v_a_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4453_: u8 = 0;
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4457_: u8 = 0;
    let mut v_p_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: u8 = 0;
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_4458_ = lean_ctor_get(v_c_u2081_4386_, 0);
                v_p_4459_ = lean_ctor_get(v_c_u2082_4388_, 0);
                v___x_4460_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9,
                );
                v___x_4461_ = lean_int_dec_le(v___x_4460_, v_a_4384_);
                if v___x_4461_ == 0 {
                    lean_inc_ref(v_p_4458_);
                    v___x_4462_ = l_Int_Linear_Poly_mul(v_p_4458_, v_b_4387_);
                    v___x_4463_ = lean_int_neg(v_a_4384_);
                    lean_inc_ref(v_p_4459_);
                    v___x_4464_ = l_Int_Linear_Poly_mul(v_p_4459_, v___x_4463_);
                    lean_dec(v___x_4463_);
                    v___x_4465_ = l_Int_Linear_Poly_combine(v___x_4462_, v___x_4464_);
                    v___y_4406_ = v___x_4465_;
                    state = 2;
                    continue;
                } else {
                    lean_inc_ref(v_p_4459_);
                    v___x_4466_ = l_Int_Linear_Poly_mul(v_p_4459_, v_a_4384_);
                    v___x_4467_ = lean_int_neg(v_b_4387_);
                    lean_inc_ref(v_p_4458_);
                    v___x_4468_ = l_Int_Linear_Poly_mul(v_p_4458_, v___x_4467_);
                    lean_dec(v___x_4467_);
                    v___x_4469_ = l_Int_Linear_Poly_combine(v___x_4466_, v___x_4468_);
                    v___y_4406_ = v___x_4469_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_4402_ = lean_alloc_ctor(10, 3, (0) as u32);
                lean_ctor_set(v___x_4402_, 0, v_x_4385_);
                lean_ctor_set(v___x_4402_, 1, v_c_u2081_4386_);
                lean_ctor_set(v___x_4402_, 2, v_c_u2082_4388_);
                v___x_4403_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4403_, 0, v___y_4401_);
                lean_ctor_set(v___x_4403_, 1, v___x_4402_);
                v___x_4404_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4404_, 0, v___x_4403_);
                return v___x_4404_;
            }
            2 => {
                v_options_4407_ = lean_ctor_get(v_a_4397_, 2);
                v_hasTrace_4408_ = lean_ctor_get_uint8(
                    v_options_4407_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_4408_ == 0 {
                    v___y_4401_ = v___y_4406_;
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_4409_ = lean_ctor_get(v_a_4397_, 13);
                    v_cls_4410_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3;
                    v___x_4411_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6,
                    );
                    v___x_4412_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_4409_,
                        v_options_4407_,
                        v___x_4411_,
                    );
                    if v___x_4412_ == 0 {
                        v___y_4401_ = v___y_4406_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4413_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(
                            v_x_4385_, v_a_4389_, v_a_4397_,
                        );
                        if lean_obj_tag(v___x_4413_) == 0 {
                            v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
                            lean_inc(v_a_4414_);
                            lean_dec_ref_known(v___x_4413_, 1);
                            lean_inc_ref(v_c_u2081_4386_);
                            v___x_4415_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(
                                v_c_u2081_4386_,
                                v_a_4389_,
                                v_a_4397_,
                            );
                            if lean_obj_tag(v___x_4415_) == 0 {
                                v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
                                lean_inc(v_a_4416_);
                                lean_dec_ref_known(v___x_4415_, 1);
                                lean_inc_ref(v_c_u2082_4388_);
                                v___x_4417_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
                                    v_c_u2082_4388_,
                                    v_a_4389_,
                                    v_a_4397_,
                                );
                                if lean_obj_tag(v___x_4417_) == 0 {
                                    v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
                                    lean_inc(v_a_4418_);
                                    lean_dec_ref_known(v___x_4417_, 1);
                                    v___x_4419_ = l_Lean_MessageData_ofExpr(v_a_4414_);
                                    v___x_4420_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8);
                                    v___x_4421_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4421_, 0, v___x_4419_);
                                    lean_ctor_set(v___x_4421_, 1, v___x_4420_);
                                    v___x_4422_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4422_, 0, v___x_4421_);
                                    lean_ctor_set(v___x_4422_, 1, v_a_4416_);
                                    v___x_4423_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4423_, 0, v___x_4422_);
                                    lean_ctor_set(v___x_4423_, 1, v___x_4420_);
                                    v___x_4424_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4424_, 0, v___x_4423_);
                                    lean_ctor_set(v___x_4424_, 1, v_a_4418_);
                                    v___x_4425_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_4410_, v___x_4424_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_);
                                    if lean_obj_tag(v___x_4425_) == 0 {
                                        lean_dec_ref_known(v___x_4425_, 1);
                                        v___y_4401_ = v___y_4406_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec_ref(v___y_4406_);
                                        lean_dec_ref(v_c_u2082_4388_);
                                        lean_dec_ref(v_c_u2081_4386_);
                                        lean_dec(v_x_4385_);
                                        v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
                                        v_isSharedCheck_4433_ =
                                            (!lean_is_exclusive(v___x_4425_)) as u8;
                                        if v_isSharedCheck_4433_ == 0 {
                                            v___x_4428_ = v___x_4425_;
                                            v_isShared_4429_ = v_isSharedCheck_4433_;
                                            state = 3;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4426_);
                                            lean_dec(v___x_4425_);
                                            v___x_4428_ = lean_box(0);
                                            v_isShared_4429_ = v_isSharedCheck_4433_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_4416_);
                                    lean_dec(v_a_4414_);
                                    lean_dec_ref(v___y_4406_);
                                    lean_dec_ref(v_c_u2082_4388_);
                                    lean_dec_ref(v_c_u2081_4386_);
                                    lean_dec(v_x_4385_);
                                    v_a_4434_ = lean_ctor_get(v___x_4417_, 0);
                                    v_isSharedCheck_4441_ = (!lean_is_exclusive(v___x_4417_)) as u8;
                                    if v_isSharedCheck_4441_ == 0 {
                                        v___x_4436_ = v___x_4417_;
                                        v_isShared_4437_ = v_isSharedCheck_4441_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4434_);
                                        lean_dec(v___x_4417_);
                                        v___x_4436_ = lean_box(0);
                                        v_isShared_4437_ = v_isSharedCheck_4441_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_4414_);
                                lean_dec_ref(v___y_4406_);
                                lean_dec_ref(v_c_u2082_4388_);
                                lean_dec_ref(v_c_u2081_4386_);
                                lean_dec(v_x_4385_);
                                v_a_4442_ = lean_ctor_get(v___x_4415_, 0);
                                v_isSharedCheck_4449_ = (!lean_is_exclusive(v___x_4415_)) as u8;
                                if v_isSharedCheck_4449_ == 0 {
                                    v___x_4444_ = v___x_4415_;
                                    v_isShared_4445_ = v_isSharedCheck_4449_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_4442_);
                                    lean_dec(v___x_4415_);
                                    v___x_4444_ = lean_box(0);
                                    v_isShared_4445_ = v_isSharedCheck_4449_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___y_4406_);
                            lean_dec_ref(v_c_u2082_4388_);
                            lean_dec_ref(v_c_u2081_4386_);
                            lean_dec(v_x_4385_);
                            v_a_4450_ = lean_ctor_get(v___x_4413_, 0);
                            v_isSharedCheck_4457_ = (!lean_is_exclusive(v___x_4413_)) as u8;
                            if v_isSharedCheck_4457_ == 0 {
                                v___x_4452_ = v___x_4413_;
                                v_isShared_4453_ = v_isSharedCheck_4457_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_4450_);
                                lean_dec(v___x_4413_);
                                v___x_4452_ = lean_box(0);
                                v_isShared_4453_ = v_isSharedCheck_4457_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                if v_isShared_4429_ == 0 {
                    v___x_4431_ = v___x_4428_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4432_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4426_);
                    v___x_4431_ = v_reuseFailAlloc_4432_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4431_;
            }
            5 => {
                if v_isShared_4437_ == 0 {
                    v___x_4439_ = v___x_4436_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4434_);
                    v___x_4439_ = v_reuseFailAlloc_4440_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4439_;
            }
            7 => {
                if v_isShared_4445_ == 0 {
                    v___x_4447_ = v___x_4444_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4448_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_a_4442_);
                    v___x_4447_ = v_reuseFailAlloc_4448_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4447_;
            }
            9 => {
                if v_isShared_4453_ == 0 {
                    v___x_4455_ = v___x_4452_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4456_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_a_4450_);
                    v___x_4455_ = v_reuseFailAlloc_4456_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4455_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___boxed(
    mut v_a_4470_: *mut LeanObject,
    mut v_x_4471_: *mut LeanObject,
    mut v_c_u2081_4472_: *mut LeanObject,
    mut v_b_4473_: *mut LeanObject,
    mut v_c_u2082_4474_: *mut LeanObject,
    mut v_a_4475_: *mut LeanObject,
    mut v_a_4476_: *mut LeanObject,
    mut v_a_4477_: *mut LeanObject,
    mut v_a_4478_: *mut LeanObject,
    mut v_a_4479_: *mut LeanObject,
    mut v_a_4480_: *mut LeanObject,
    mut v_a_4481_: *mut LeanObject,
    mut v_a_4482_: *mut LeanObject,
    mut v_a_4483_: *mut LeanObject,
    mut v_a_4484_: *mut LeanObject,
    mut v_a_4485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4486_: *mut LeanObject = core::ptr::null_mut();
    v_res_4486_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(
        v_a_4470_,
        v_x_4471_,
        v_c_u2081_4472_,
        v_b_4473_,
        v_c_u2082_4474_,
        v_a_4475_,
        v_a_4476_,
        v_a_4477_,
        v_a_4478_,
        v_a_4479_,
        v_a_4480_,
        v_a_4481_,
        v_a_4482_,
        v_a_4483_,
        v_a_4484_,
    );
    lean_dec(v_a_4484_);
    lean_dec_ref(v_a_4483_);
    lean_dec(v_a_4482_);
    lean_dec_ref(v_a_4481_);
    lean_dec(v_a_4480_);
    lean_dec_ref(v_a_4479_);
    lean_dec(v_a_4478_);
    lean_dec_ref(v_a_4477_);
    lean_dec(v_a_4476_);
    lean_dec(v_a_4475_);
    lean_dec(v_b_4473_);
    lean_dec(v_a_4470_);
    return v_res_4486_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0(
    mut v_cls_4487_: *mut LeanObject,
    mut v_msg_4488_: *mut LeanObject,
    mut v___y_4489_: *mut LeanObject,
    mut v___y_4490_: *mut LeanObject,
    mut v___y_4491_: *mut LeanObject,
    mut v___y_4492_: *mut LeanObject,
    mut v___y_4493_: *mut LeanObject,
    mut v___y_4494_: *mut LeanObject,
    mut v___y_4495_: *mut LeanObject,
    mut v___y_4496_: *mut LeanObject,
    mut v___y_4497_: *mut LeanObject,
    mut v___y_4498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    v___x_4500_ =
        l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(
            v_cls_4487_,
            v_msg_4488_,
            v___y_4495_,
            v___y_4496_,
            v___y_4497_,
            v___y_4498_,
        );
    return v___x_4500_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___boxed(
    mut v_cls_4501_: *mut LeanObject,
    mut v_msg_4502_: *mut LeanObject,
    mut v___y_4503_: *mut LeanObject,
    mut v___y_4504_: *mut LeanObject,
    mut v___y_4505_: *mut LeanObject,
    mut v___y_4506_: *mut LeanObject,
    mut v___y_4507_: *mut LeanObject,
    mut v___y_4508_: *mut LeanObject,
    mut v___y_4509_: *mut LeanObject,
    mut v___y_4510_: *mut LeanObject,
    mut v___y_4511_: *mut LeanObject,
    mut v___y_4512_: *mut LeanObject,
    mut v___y_4513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4514_: *mut LeanObject = core::ptr::null_mut();
    v_res_4514_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0(
        v_cls_4501_,
        v_msg_4502_,
        v___y_4503_,
        v___y_4504_,
        v___y_4505_,
        v___y_4506_,
        v___y_4507_,
        v___y_4508_,
        v___y_4509_,
        v___y_4510_,
        v___y_4511_,
        v___y_4512_,
    );
    lean_dec(v___y_4512_);
    lean_dec_ref(v___y_4511_);
    lean_dec(v___y_4510_);
    lean_dec_ref(v___y_4509_);
    lean_dec(v___y_4508_);
    lean_dec_ref(v___y_4507_);
    lean_dec(v___y_4506_);
    lean_dec_ref(v___y_4505_);
    lean_dec(v___y_4504_);
    lean_dec(v___y_4503_);
    return v_res_4514_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    v___x_4520_ = l_Lean_maxRecDepthErrorMessage;
    v___x_4521_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_4521_, 0, v___x_4520_);
    return v___x_4521_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    v___x_4522_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3);
    v___x_4523_ = l_Lean_MessageData_ofFormat(v___x_4522_);
    return v___x_4523_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    v___x_4524_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4);
    v___x_4525_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__2;
    v___x_4526_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_4526_, 0, v___x_4525_);
    lean_ctor_set(v___x_4526_, 1, v___x_4524_);
    return v___x_4526_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(
    mut v_ref_4527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    v___x_4529_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5);
    v___x_4530_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4530_, 0, v_ref_4527_);
    lean_ctor_set(v___x_4530_, 1, v___x_4529_);
    v___x_4531_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4531_, 0, v___x_4530_);
    return v___x_4531_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___boxed(
    mut v_ref_4532_: *mut LeanObject,
    mut v___y_4533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4534_: *mut LeanObject = core::ptr::null_mut();
    v_res_4534_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_4532_);
    return v_res_4534_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0(
    mut v_00_u03b1_4535_: *mut LeanObject,
    mut v_ref_4536_: *mut LeanObject,
    mut v___y_4537_: *mut LeanObject,
    mut v___y_4538_: *mut LeanObject,
    mut v___y_4539_: *mut LeanObject,
    mut v___y_4540_: *mut LeanObject,
    mut v___y_4541_: *mut LeanObject,
    mut v___y_4542_: *mut LeanObject,
    mut v___y_4543_: *mut LeanObject,
    mut v___y_4544_: *mut LeanObject,
    mut v___y_4545_: *mut LeanObject,
    mut v___y_4546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    v___x_4548_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_4536_);
    return v___x_4548_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___boxed(
    mut v_00_u03b1_4549_: *mut LeanObject,
    mut v_ref_4550_: *mut LeanObject,
    mut v___y_4551_: *mut LeanObject,
    mut v___y_4552_: *mut LeanObject,
    mut v___y_4553_: *mut LeanObject,
    mut v___y_4554_: *mut LeanObject,
    mut v___y_4555_: *mut LeanObject,
    mut v___y_4556_: *mut LeanObject,
    mut v___y_4557_: *mut LeanObject,
    mut v___y_4558_: *mut LeanObject,
    mut v___y_4559_: *mut LeanObject,
    mut v___y_4560_: *mut LeanObject,
    mut v___y_4561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4562_: *mut LeanObject = core::ptr::null_mut();
    v_res_4562_ =
        l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0(
            v_00_u03b1_4549_,
            v_ref_4550_,
            v___y_4551_,
            v___y_4552_,
            v___y_4553_,
            v___y_4554_,
            v___y_4555_,
            v___y_4556_,
            v___y_4557_,
            v___y_4558_,
            v___y_4559_,
            v___y_4560_,
        );
    lean_dec(v___y_4560_);
    lean_dec_ref(v___y_4559_);
    lean_dec(v___y_4558_);
    lean_dec_ref(v___y_4557_);
    lean_dec(v___y_4556_);
    lean_dec_ref(v___y_4555_);
    lean_dec(v___y_4554_);
    lean_dec_ref(v___y_4553_);
    lean_dec(v___y_4552_);
    lean_dec(v___y_4551_);
    return v_res_4562_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(
    mut v_c_4563_: *mut LeanObject,
    mut v_a_4564_: *mut LeanObject,
    mut v_a_4565_: *mut LeanObject,
    mut v_a_4566_: *mut LeanObject,
    mut v_a_4567_: *mut LeanObject,
    mut v_a_4568_: *mut LeanObject,
    mut v_a_4569_: *mut LeanObject,
    mut v_a_4570_: *mut LeanObject,
    mut v_a_4571_: *mut LeanObject,
    mut v_a_4572_: *mut LeanObject,
    mut v_a_4573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4588_: u8 = 0;
    let mut v_cancelTk_x3f_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4590_: u8 = 0;
    let mut v_inheritedTraceOptions_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4600_: u8 = 0;
    let mut v_val_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4614_: u8 = 0;
    let mut v_a_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4618_: u8 = 0;
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4622_: u8 = 0;
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: u8 = 0;
    let mut v___x_4625_: u8 = 0;
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_4575_ = lean_ctor_get(v_c_4563_, 0);
                v_fileName_4576_ = lean_ctor_get(v_a_4572_, 0);
                lean_inc_ref(v_fileName_4576_);
                v_fileMap_4577_ = lean_ctor_get(v_a_4572_, 1);
                lean_inc_ref(v_fileMap_4577_);
                v_options_4578_ = lean_ctor_get(v_a_4572_, 2);
                lean_inc_ref(v_options_4578_);
                v_currRecDepth_4579_ = lean_ctor_get(v_a_4572_, 3);
                lean_inc(v_currRecDepth_4579_);
                v_maxRecDepth_4580_ = lean_ctor_get(v_a_4572_, 4);
                lean_inc(v_maxRecDepth_4580_);
                v_ref_4581_ = lean_ctor_get(v_a_4572_, 5);
                lean_inc(v_ref_4581_);
                v_currNamespace_4582_ = lean_ctor_get(v_a_4572_, 6);
                lean_inc(v_currNamespace_4582_);
                v_openDecls_4583_ = lean_ctor_get(v_a_4572_, 7);
                lean_inc(v_openDecls_4583_);
                v_initHeartbeats_4584_ = lean_ctor_get(v_a_4572_, 8);
                lean_inc(v_initHeartbeats_4584_);
                v_maxHeartbeats_4585_ = lean_ctor_get(v_a_4572_, 9);
                lean_inc(v_maxHeartbeats_4585_);
                v_quotContext_4586_ = lean_ctor_get(v_a_4572_, 10);
                lean_inc(v_quotContext_4586_);
                v_currMacroScope_4587_ = lean_ctor_get(v_a_4572_, 11);
                lean_inc(v_currMacroScope_4587_);
                v_diag_4588_ = lean_ctor_get_uint8(
                    v_a_4572_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4589_ = lean_ctor_get(v_a_4572_, 12);
                lean_inc(v_cancelTk_x3f_4589_);
                v_suppressElabErrors_4590_ = lean_ctor_get_uint8(
                    v_a_4572_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4591_ = lean_ctor_get(v_a_4572_, 13);
                lean_inc_ref(v_inheritedTraceOptions_4591_);
                lean_dec_ref(v_a_4572_);
                v___x_4623_ = lean_unsigned_to_nat(0);
                v___x_4624_ = lean_nat_dec_eq(v_maxRecDepth_4580_, v___x_4623_);
                if v___x_4624_ == 0 {
                    v___x_4625_ = lean_nat_dec_eq(v_currRecDepth_4579_, v_maxRecDepth_4580_);
                    if v___x_4625_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_inheritedTraceOptions_4591_);
                        lean_dec(v_cancelTk_x3f_4589_);
                        lean_dec(v_currMacroScope_4587_);
                        lean_dec(v_quotContext_4586_);
                        lean_dec(v_maxHeartbeats_4585_);
                        lean_dec(v_initHeartbeats_4584_);
                        lean_dec(v_openDecls_4583_);
                        lean_dec(v_currNamespace_4582_);
                        lean_dec(v_maxRecDepth_4580_);
                        lean_dec(v_currRecDepth_4579_);
                        lean_dec_ref(v_options_4578_);
                        lean_dec_ref(v_fileMap_4577_);
                        lean_dec_ref(v_fileName_4576_);
                        lean_dec_ref(v_c_4563_);
                        v___x_4626_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_4581_);
                        return v___x_4626_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4593_ = lean_unsigned_to_nat(1);
                v___x_4594_ = lean_nat_add(v_currRecDepth_4579_, v___x_4593_);
                lean_dec(v_currRecDepth_4579_);
                v___x_4595_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_4595_, 0, v_fileName_4576_);
                lean_ctor_set(v___x_4595_, 1, v_fileMap_4577_);
                lean_ctor_set(v___x_4595_, 2, v_options_4578_);
                lean_ctor_set(v___x_4595_, 3, v___x_4594_);
                lean_ctor_set(v___x_4595_, 4, v_maxRecDepth_4580_);
                lean_ctor_set(v___x_4595_, 5, v_ref_4581_);
                lean_ctor_set(v___x_4595_, 6, v_currNamespace_4582_);
                lean_ctor_set(v___x_4595_, 7, v_openDecls_4583_);
                lean_ctor_set(v___x_4595_, 8, v_initHeartbeats_4584_);
                lean_ctor_set(v___x_4595_, 9, v_maxHeartbeats_4585_);
                lean_ctor_set(v___x_4595_, 10, v_quotContext_4586_);
                lean_ctor_set(v___x_4595_, 11, v_currMacroScope_4587_);
                lean_ctor_set(v___x_4595_, 12, v_cancelTk_x3f_4589_);
                lean_ctor_set(v___x_4595_, 13, v_inheritedTraceOptions_4591_);
                lean_ctor_set_uint8(
                    v___x_4595_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_4588_,
                );
                lean_ctor_set_uint8(
                    v___x_4595_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4590_,
                );
                lean_inc_ref(v_p_4575_);
                v___x_4596_ =
                    l_Int_Linear_Poly_findVarToSubst___redArg(v_p_4575_, v_a_4564_, v___x_4595_);
                if lean_obj_tag(v___x_4596_) == 0 {
                    v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
                    v_isSharedCheck_4614_ = (!lean_is_exclusive(v___x_4596_)) as u8;
                    if v_isSharedCheck_4614_ == 0 {
                        v___x_4599_ = v___x_4596_;
                        v_isShared_4600_ = v_isSharedCheck_4614_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4597_);
                        lean_dec(v___x_4596_);
                        v___x_4599_ = lean_box(0);
                        v_isShared_4600_ = v_isSharedCheck_4614_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_4595_, 14);
                    lean_dec_ref(v_c_4563_);
                    v_a_4615_ = lean_ctor_get(v___x_4596_, 0);
                    v_isSharedCheck_4622_ = (!lean_is_exclusive(v___x_4596_)) as u8;
                    if v_isSharedCheck_4622_ == 0 {
                        v___x_4617_ = v___x_4596_;
                        v_isShared_4618_ = v_isSharedCheck_4622_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4615_);
                        lean_dec(v___x_4596_);
                        v___x_4617_ = lean_box(0);
                        v_isShared_4618_ = v_isSharedCheck_4622_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_4597_) == 1 {
                    lean_del_object(v___x_4599_);
                    v_val_4601_ = lean_ctor_get(v_a_4597_, 0);
                    lean_inc(v_val_4601_);
                    lean_dec_ref_known(v_a_4597_, 1);
                    v_snd_4602_ = lean_ctor_get(v_val_4601_, 1);
                    lean_inc(v_snd_4602_);
                    v_snd_4603_ = lean_ctor_get(v_snd_4602_, 1);
                    lean_inc(v_snd_4603_);
                    v_fst_4604_ = lean_ctor_get(v_val_4601_, 0);
                    lean_inc(v_fst_4604_);
                    lean_dec(v_val_4601_);
                    v_fst_4605_ = lean_ctor_get(v_snd_4602_, 0);
                    lean_inc(v_fst_4605_);
                    lean_dec(v_snd_4602_);
                    v_p_4606_ = lean_ctor_get(v_snd_4603_, 0);
                    v___x_4607_ = l_Int_Linear_Poly_coeff(v_p_4606_, v_fst_4605_);
                    v___x_4608_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(
                        v___x_4607_,
                        v_fst_4605_,
                        v_snd_4603_,
                        v_fst_4604_,
                        v_c_4563_,
                        v_a_4564_,
                        v_a_4565_,
                        v_a_4566_,
                        v_a_4567_,
                        v_a_4568_,
                        v_a_4569_,
                        v_a_4570_,
                        v_a_4571_,
                        v___x_4595_,
                        v_a_4573_,
                    );
                    lean_dec(v_fst_4604_);
                    lean_dec(v___x_4607_);
                    if lean_obj_tag(v___x_4608_) == 0 {
                        v_a_4609_ = lean_ctor_get(v___x_4608_, 0);
                        lean_inc(v_a_4609_);
                        lean_dec_ref_known(v___x_4608_, 1);
                        v_c_4563_ = v_a_4609_;
                        v_a_4572_ = v___x_4595_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref_known(v___x_4595_, 14);
                        return v___x_4608_;
                    }
                } else {
                    lean_dec(v_a_4597_);
                    lean_dec_ref_known(v___x_4595_, 14);
                    if v_isShared_4600_ == 0 {
                        lean_ctor_set(v___x_4599_, 0, v_c_4563_);
                        v___x_4612_ = v___x_4599_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_c_4563_);
                        v___x_4612_ = v_reuseFailAlloc_4613_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4612_;
            }
            4 => {
                if v_isShared_4618_ == 0 {
                    v___x_4620_ = v___x_4617_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4621_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_a_4615_);
                    v___x_4620_ = v_reuseFailAlloc_4621_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4620_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___boxed(
    mut v_c_4627_: *mut LeanObject,
    mut v_a_4628_: *mut LeanObject,
    mut v_a_4629_: *mut LeanObject,
    mut v_a_4630_: *mut LeanObject,
    mut v_a_4631_: *mut LeanObject,
    mut v_a_4632_: *mut LeanObject,
    mut v_a_4633_: *mut LeanObject,
    mut v_a_4634_: *mut LeanObject,
    mut v_a_4635_: *mut LeanObject,
    mut v_a_4636_: *mut LeanObject,
    mut v_a_4637_: *mut LeanObject,
    mut v_a_4638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4639_: *mut LeanObject = core::ptr::null_mut();
    v_res_4639_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(
        v_c_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_,
        v_a_4635_, v_a_4636_, v_a_4637_,
    );
    lean_dec(v_a_4637_);
    lean_dec(v_a_4635_);
    lean_dec_ref(v_a_4634_);
    lean_dec(v_a_4633_);
    lean_dec_ref(v_a_4632_);
    lean_dec(v_a_4631_);
    lean_dec_ref(v_a_4630_);
    lean_dec(v_a_4629_);
    lean_dec(v_a_4628_);
    return v_res_4639_;
}
pub unsafe fn l_Int_Linear_Poly_isNegEq(
    mut v_p_u2081_4640_: *mut LeanObject,
    mut v_p_u2082_4641_: *mut LeanObject,
) -> u8 {
    let mut v_k_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: u8 = 0;
    let mut v___x_4646_: u8 = 0;
    let mut v_k_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4654_: u8 = 0;
    let mut v___x_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: u8 = 0;
    let mut v___x_4658_: u8 = 0;
    let mut v___x_4659_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_u2081_4640_) == 0 {
                    if lean_obj_tag(v_p_u2082_4641_) == 0 {
                        v_k_4642_ = lean_ctor_get(v_p_u2081_4640_, 0);
                        v_k_4643_ = lean_ctor_get(v_p_u2082_4641_, 0);
                        v___x_4644_ = lean_int_neg(v_k_4643_);
                        v___x_4645_ = lean_int_dec_eq(v_k_4642_, v___x_4644_);
                        lean_dec(v___x_4644_);
                        return v___x_4645_;
                    } else {
                        v___x_4646_ = 0;
                        return v___x_4646_;
                    }
                } else {
                    if lean_obj_tag(v_p_u2082_4641_) == 1 {
                        v_k_4647_ = lean_ctor_get(v_p_u2081_4640_, 0);
                        v_v_4648_ = lean_ctor_get(v_p_u2081_4640_, 1);
                        v_p_4649_ = lean_ctor_get(v_p_u2081_4640_, 2);
                        v_k_4650_ = lean_ctor_get(v_p_u2082_4641_, 0);
                        v_v_4651_ = lean_ctor_get(v_p_u2082_4641_, 1);
                        v_p_4652_ = lean_ctor_get(v_p_u2082_4641_, 2);
                        v___x_4656_ = lean_int_neg(v_k_4650_);
                        v___x_4657_ = lean_int_dec_eq(v_k_4647_, v___x_4656_);
                        lean_dec(v___x_4656_);
                        if v___x_4657_ == 0 {
                            v___y_4654_ = v___x_4657_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4658_ = lean_nat_dec_eq(v_v_4648_, v_v_4651_);
                            v___y_4654_ = v___x_4658_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_4659_ = 0;
                        return v___x_4659_;
                    }
                }
            }
            1 => {
                if v___y_4654_ == 0 {
                    return v___y_4654_;
                } else {
                    v_p_u2081_4640_ = v_p_4649_;
                    v_p_u2082_4641_ = v_p_4652_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_isNegEq___boxed(
    mut v_p_u2081_4660_: *mut LeanObject,
    mut v_p_u2082_4661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4662_: u8 = 0;
    let mut v_r_4663_: *mut LeanObject = core::ptr::null_mut();
    v_res_4662_ = l_Int_Linear_Poly_isNegEq(v_p_u2081_4660_, v_p_u2082_4661_);
    lean_dec_ref(v_p_u2082_4661_);
    lean_dec_ref(v_p_u2081_4660_);
    v_r_4663_ = lean_box((v_res_4662_) as usize);
    return v_r_4663_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(
    mut v___x_4664_: *mut LeanObject,
    mut v_as_4665_: *mut LeanObject,
    mut v_i_4666_: usize,
    mut v_stop_4667_: usize,
    mut v_b_4668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: usize = 0;
    let mut v___x_4672_: usize = 0;
    let mut v___x_4674_: u8 = 0;
    let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: u8 = 0;
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4674_ = lean_usize_dec_eq(v_i_4666_, v_stop_4667_);
                if v___x_4674_ == 0 {
                    v___x_4675_ = lean_array_uget_borrowed(v_as_4665_, v_i_4666_);
                    v_p_4676_ = lean_ctor_get(v___x_4675_, 0);
                    v___x_4677_ = l_Int_Linear_instBEqPoly_beq(v_p_4676_, v___x_4664_);
                    if v___x_4677_ == 0 {
                        lean_inc(v___x_4675_);
                        v___x_4678_ = l_Lean_PersistentArray_push___redArg(v_b_4668_, v___x_4675_);
                        v___y_4670_ = v___x_4678_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4670_ = v_b_4668_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_4668_;
                }
            }
            1 => {
                v___x_4671_ = 1usize;
                v___x_4672_ = lean_usize_add(v_i_4666_, v___x_4671_);
                v_i_4666_ = v___x_4672_;
                v_b_4668_ = v___y_4670_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1___boxed(
    mut v___x_4679_: *mut LeanObject,
    mut v_as_4680_: *mut LeanObject,
    mut v_i_4681_: *mut LeanObject,
    mut v_stop_4682_: *mut LeanObject,
    mut v_b_4683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4684_: usize = 0;
    let mut v_stop_boxed_4685_: usize = 0;
    let mut v_res_4686_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4684_ = lean_unbox_usize(v_i_4681_);
    lean_dec(v_i_4681_);
    v_stop_boxed_4685_ = lean_unbox_usize(v_stop_4682_);
    lean_dec(v_stop_4682_);
    v_res_4686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_4679_, v_as_4680_, v_i_boxed_4684_, v_stop_boxed_4685_, v_b_4683_);
    lean_dec_ref(v_as_4680_);
    lean_dec_ref(v___x_4679_);
    return v_res_4686_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(
    mut v___x_4687_: *mut LeanObject,
    mut v_x_4688_: *mut LeanObject,
    mut v_x_4689_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4688_) == 0 {
        let mut v_cs_4690_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4693_: u8 = 0;
        v_cs_4690_ = lean_ctor_get(v_x_4688_, 0);
        v___x_4691_ = lean_unsigned_to_nat(0);
        v___x_4692_ = lean_array_get_size(v_cs_4690_);
        v___x_4693_ = lean_nat_dec_lt(v___x_4691_, v___x_4692_);
        if v___x_4693_ == 0 {
            return v_x_4689_;
        } else {
            let mut v___x_4694_: u8 = 0;
            v___x_4694_ = lean_nat_dec_le(v___x_4692_, v___x_4692_);
            if v___x_4694_ == 0 {
                if v___x_4693_ == 0 {
                    return v_x_4689_;
                } else {
                    let mut v___x_4695_: usize = 0;
                    let mut v___x_4696_: usize = 0;
                    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4695_ = 0usize;
                    v___x_4696_ = lean_usize_of_nat(v___x_4692_);
                    v___x_4697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_4687_, v_cs_4690_, v___x_4695_, v___x_4696_, v_x_4689_);
                    return v___x_4697_;
                }
            } else {
                let mut v___x_4698_: usize = 0;
                let mut v___x_4699_: usize = 0;
                let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
                v___x_4698_ = 0usize;
                v___x_4699_ = lean_usize_of_nat(v___x_4692_);
                v___x_4700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_4687_, v_cs_4690_, v___x_4698_, v___x_4699_, v_x_4689_);
                return v___x_4700_;
            }
        }
    } else {
        let mut v_vs_4701_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4703_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4704_: u8 = 0;
        v_vs_4701_ = lean_ctor_get(v_x_4688_, 0);
        v___x_4702_ = lean_unsigned_to_nat(0);
        v___x_4703_ = lean_array_get_size(v_vs_4701_);
        v___x_4704_ = lean_nat_dec_lt(v___x_4702_, v___x_4703_);
        if v___x_4704_ == 0 {
            return v_x_4689_;
        } else {
            let mut v___x_4705_: u8 = 0;
            v___x_4705_ = lean_nat_dec_le(v___x_4703_, v___x_4703_);
            if v___x_4705_ == 0 {
                if v___x_4704_ == 0 {
                    return v_x_4689_;
                } else {
                    let mut v___x_4706_: usize = 0;
                    let mut v___x_4707_: usize = 0;
                    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4706_ = 0usize;
                    v___x_4707_ = lean_usize_of_nat(v___x_4703_);
                    v___x_4708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_4687_, v_vs_4701_, v___x_4706_, v___x_4707_, v_x_4689_);
                    return v___x_4708_;
                }
            } else {
                let mut v___x_4709_: usize = 0;
                let mut v___x_4710_: usize = 0;
                let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
                v___x_4709_ = 0usize;
                v___x_4710_ = lean_usize_of_nat(v___x_4703_);
                v___x_4711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_4687_, v_vs_4701_, v___x_4709_, v___x_4710_, v_x_4689_);
                return v___x_4711_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(
    mut v___x_4712_: *mut LeanObject,
    mut v_as_4713_: *mut LeanObject,
    mut v_i_4714_: usize,
    mut v_stop_4715_: usize,
    mut v_b_4716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4717_: u8 = 0;
    let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: usize = 0;
    let mut v___x_4721_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4717_ = lean_usize_dec_eq(v_i_4714_, v_stop_4715_);
                if v___x_4717_ == 0 {
                    v___x_4718_ = lean_array_uget_borrowed(v_as_4713_, v_i_4714_);
                    v___x_4719_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_4712_, v___x_4718_, v_b_4716_);
                    v___x_4720_ = 1usize;
                    v___x_4721_ = lean_usize_add(v_i_4714_, v___x_4720_);
                    v_i_4714_ = v___x_4721_;
                    v_b_4716_ = v___x_4719_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4716_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1___boxed(
    mut v___x_4723_: *mut LeanObject,
    mut v_as_4724_: *mut LeanObject,
    mut v_i_4725_: *mut LeanObject,
    mut v_stop_4726_: *mut LeanObject,
    mut v_b_4727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4728_: usize = 0;
    let mut v_stop_boxed_4729_: usize = 0;
    let mut v_res_4730_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4728_ = lean_unbox_usize(v_i_4725_);
    lean_dec(v_i_4725_);
    v_stop_boxed_4729_ = lean_unbox_usize(v_stop_4726_);
    lean_dec(v_stop_4726_);
    v_res_4730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_4723_, v_as_4724_, v_i_boxed_4728_, v_stop_boxed_4729_, v_b_4727_);
    lean_dec_ref(v_as_4724_);
    lean_dec_ref(v___x_4723_);
    return v_res_4730_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2___boxed(
    mut v___x_4731_: *mut LeanObject,
    mut v_x_4732_: *mut LeanObject,
    mut v_x_4733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4734_: *mut LeanObject = core::ptr::null_mut();
    v_res_4734_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_4731_, v_x_4732_, v_x_4733_);
    lean_dec_ref(v_x_4732_);
    lean_dec_ref(v___x_4731_);
    return v_res_4734_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    v___x_4735_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
    return v___x_4735_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(
    mut v___x_4736_: *mut LeanObject,
    mut v_x_4737_: *mut LeanObject,
    mut v_x_4738_: usize,
    mut v_x_4739_: usize,
    mut v_x_4740_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4737_) == 0 {
        let mut v_cs_4741_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4742_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4743_: usize = 0;
        let mut v_j_4744_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4746_: usize = 0;
        let mut v___x_4747_: usize = 0;
        let mut v___x_4748_: usize = 0;
        let mut v___x_4749_: usize = 0;
        let mut v___x_4750_: usize = 0;
        let mut v___x_4751_: usize = 0;
        let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4756_: u8 = 0;
        v_cs_4741_ = lean_ctor_get(v_x_4737_, 0);
        v___x_4742_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
        v___x_4743_ = lean_usize_shift_right(v_x_4738_, v_x_4739_);
        v_j_4744_ = lean_usize_to_nat(v___x_4743_);
        v___x_4745_ = lean_array_get_borrowed(v___x_4742_, v_cs_4741_, v_j_4744_);
        v___x_4746_ = 1usize;
        v___x_4747_ = lean_usize_shift_left(v___x_4746_, v_x_4739_);
        v___x_4748_ = lean_usize_sub(v___x_4747_, v___x_4746_);
        v___x_4749_ = lean_usize_land(v_x_4738_, v___x_4748_);
        v___x_4750_ = 5usize;
        v___x_4751_ = lean_usize_sub(v_x_4739_, v___x_4750_);
        v___x_4752_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_4736_, v___x_4745_, v___x_4749_, v___x_4751_, v_x_4740_);
        v___x_4753_ = lean_unsigned_to_nat(1);
        v___x_4754_ = lean_nat_add(v_j_4744_, v___x_4753_);
        lean_dec(v_j_4744_);
        v___x_4755_ = lean_array_get_size(v_cs_4741_);
        v___x_4756_ = lean_nat_dec_lt(v___x_4754_, v___x_4755_);
        if v___x_4756_ == 0 {
            lean_dec(v___x_4754_);
            return v___x_4752_;
        } else {
            let mut v___x_4757_: u8 = 0;
            v___x_4757_ = lean_nat_dec_le(v___x_4755_, v___x_4755_);
            if v___x_4757_ == 0 {
                if v___x_4756_ == 0 {
                    lean_dec(v___x_4754_);
                    return v___x_4752_;
                } else {
                    let mut v___x_4758_: usize = 0;
                    let mut v___x_4759_: usize = 0;
                    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4758_ = lean_usize_of_nat(v___x_4754_);
                    lean_dec(v___x_4754_);
                    v___x_4759_ = lean_usize_of_nat(v___x_4755_);
                    v___x_4760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_4736_, v_cs_4741_, v___x_4758_, v___x_4759_, v___x_4752_);
                    return v___x_4760_;
                }
            } else {
                let mut v___x_4761_: usize = 0;
                let mut v___x_4762_: usize = 0;
                let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
                v___x_4761_ = lean_usize_of_nat(v___x_4754_);
                lean_dec(v___x_4754_);
                v___x_4762_ = lean_usize_of_nat(v___x_4755_);
                v___x_4763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_4736_, v_cs_4741_, v___x_4761_, v___x_4762_, v___x_4752_);
                return v___x_4763_;
            }
        }
    } else {
        let mut v_vs_4764_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4767_: u8 = 0;
        v_vs_4764_ = lean_ctor_get(v_x_4737_, 0);
        v___x_4765_ = lean_usize_to_nat(v_x_4738_);
        v___x_4766_ = lean_array_get_size(v_vs_4764_);
        v___x_4767_ = lean_nat_dec_lt(v___x_4765_, v___x_4766_);
        if v___x_4767_ == 0 {
            lean_dec(v___x_4765_);
            return v_x_4740_;
        } else {
            let mut v___x_4768_: u8 = 0;
            v___x_4768_ = lean_nat_dec_le(v___x_4766_, v___x_4766_);
            if v___x_4768_ == 0 {
                if v___x_4767_ == 0 {
                    lean_dec(v___x_4765_);
                    return v_x_4740_;
                } else {
                    let mut v___x_4769_: usize = 0;
                    let mut v___x_4770_: usize = 0;
                    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4769_ = lean_usize_of_nat(v___x_4765_);
                    lean_dec(v___x_4765_);
                    v___x_4770_ = lean_usize_of_nat(v___x_4766_);
                    v___x_4771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_4736_, v_vs_4764_, v___x_4769_, v___x_4770_, v_x_4740_);
                    return v___x_4771_;
                }
            } else {
                let mut v___x_4772_: usize = 0;
                let mut v___x_4773_: usize = 0;
                let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
                v___x_4772_ = lean_usize_of_nat(v___x_4765_);
                lean_dec(v___x_4765_);
                v___x_4773_ = lean_usize_of_nat(v___x_4766_);
                v___x_4774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_4736_, v_vs_4764_, v___x_4772_, v___x_4773_, v_x_4740_);
                return v___x_4774_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___boxed(
    mut v___x_4775_: *mut LeanObject,
    mut v_x_4776_: *mut LeanObject,
    mut v_x_4777_: *mut LeanObject,
    mut v_x_4778_: *mut LeanObject,
    mut v_x_4779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2065__boxed_4780_: usize = 0;
    let mut v_x_2066__boxed_4781_: usize = 0;
    let mut v_res_4782_: *mut LeanObject = core::ptr::null_mut();
    v_x_2065__boxed_4780_ = lean_unbox_usize(v_x_4777_);
    lean_dec(v_x_4777_);
    v_x_2066__boxed_4781_ = lean_unbox_usize(v_x_4778_);
    lean_dec(v_x_4778_);
    v_res_4782_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_4775_, v_x_4776_, v_x_2065__boxed_4780_, v_x_2066__boxed_4781_, v_x_4779_);
    lean_dec_ref(v_x_4776_);
    lean_dec_ref(v___x_4775_);
    return v_res_4782_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(
    mut v___x_4783_: *mut LeanObject,
    mut v_t_4784_: *mut LeanObject,
    mut v_init_4785_: *mut LeanObject,
    mut v_start_4786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: u8 = 0;
    v___x_4787_ = lean_unsigned_to_nat(0);
    v___x_4788_ = lean_nat_dec_eq(v_start_4786_, v___x_4787_);
    if v___x_4788_ == 0 {
        let mut v_root_4789_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_4790_: *mut LeanObject = core::ptr::null_mut();
        let mut v_shift_4791_: usize = 0;
        let mut v_tailOff_4792_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4793_: u8 = 0;
        v_root_4789_ = lean_ctor_get(v_t_4784_, 0);
        v_tail_4790_ = lean_ctor_get(v_t_4784_, 1);
        v_shift_4791_ = lean_ctor_get_usize(v_t_4784_, 4);
        v_tailOff_4792_ = lean_ctor_get(v_t_4784_, 3);
        v___x_4793_ = lean_nat_dec_le(v_tailOff_4792_, v_start_4786_);
        if v___x_4793_ == 0 {
            let mut v___x_4794_: usize = 0;
            let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4797_: u8 = 0;
            v___x_4794_ = lean_usize_of_nat(v_start_4786_);
            v___x_4795_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_4783_, v_root_4789_, v___x_4794_, v_shift_4791_, v_init_4785_);
            v___x_4796_ = lean_array_get_size(v_tail_4790_);
            v___x_4797_ = lean_nat_dec_lt(v___x_4787_, v___x_4796_);
            if v___x_4797_ == 0 {
                return v___x_4795_;
            } else {
                let mut v___x_4798_: u8 = 0;
                v___x_4798_ = lean_nat_dec_le(v___x_4796_, v___x_4796_);
                if v___x_4798_ == 0 {
                    if v___x_4797_ == 0 {
                        return v___x_4795_;
                    } else {
                        let mut v___x_4799_: usize = 0;
                        let mut v___x_4800_: usize = 0;
                        let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
                        v___x_4799_ = 0usize;
                        v___x_4800_ = lean_usize_of_nat(v___x_4796_);
                        v___x_4801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_4783_, v_tail_4790_, v___x_4799_, v___x_4800_, v___x_4795_);
                        return v___x_4801_;
                    }
                } else {
                    let mut v___x_4802_: usize = 0;
                    let mut v___x_4803_: usize = 0;
                    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4802_ = 0usize;
                    v___x_4803_ = lean_usize_of_nat(v___x_4796_);
                    v___x_4804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_4783_, v_tail_4790_, v___x_4802_, v___x_4803_, v___x_4795_);
                    return v___x_4804_;
                }
            }
        } else {
            let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4807_: u8 = 0;
            v___x_4805_ = lean_nat_sub(v_start_4786_, v_tailOff_4792_);
            v___x_4806_ = lean_array_get_size(v_tail_4790_);
            v___x_4807_ = lean_nat_dec_lt(v___x_4805_, v___x_4806_);
            if v___x_4807_ == 0 {
                lean_dec(v___x_4805_);
                return v_init_4785_;
            } else {
                let mut v___x_4808_: u8 = 0;
                v___x_4808_ = lean_nat_dec_le(v___x_4806_, v___x_4806_);
                if v___x_4808_ == 0 {
                    if v___x_4807_ == 0 {
                        lean_dec(v___x_4805_);
                        return v_init_4785_;
                    } else {
                        let mut v___x_4809_: usize = 0;
                        let mut v___x_4810_: usize = 0;
                        let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
                        v___x_4809_ = lean_usize_of_nat(v___x_4805_);
                        lean_dec(v___x_4805_);
                        v___x_4810_ = lean_usize_of_nat(v___x_4806_);
                        v___x_4811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_4783_, v_tail_4790_, v___x_4809_, v___x_4810_, v_init_4785_);
                        return v___x_4811_;
                    }
                } else {
                    let mut v___x_4812_: usize = 0;
                    let mut v___x_4813_: usize = 0;
                    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4812_ = lean_usize_of_nat(v___x_4805_);
                    lean_dec(v___x_4805_);
                    v___x_4813_ = lean_usize_of_nat(v___x_4806_);
                    v___x_4814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_4783_, v_tail_4790_, v___x_4812_, v___x_4813_, v_init_4785_);
                    return v___x_4814_;
                }
            }
        }
    } else {
        let mut v_root_4815_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_4816_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4819_: u8 = 0;
        v_root_4815_ = lean_ctor_get(v_t_4784_, 0);
        v_tail_4816_ = lean_ctor_get(v_t_4784_, 1);
        v___x_4817_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_4783_, v_root_4815_, v_init_4785_);
        v___x_4818_ = lean_array_get_size(v_tail_4816_);
        v___x_4819_ = lean_nat_dec_lt(v___x_4787_, v___x_4818_);
        if v___x_4819_ == 0 {
            return v___x_4817_;
        } else {
            let mut v___x_4820_: u8 = 0;
            v___x_4820_ = lean_nat_dec_le(v___x_4818_, v___x_4818_);
            if v___x_4820_ == 0 {
                if v___x_4819_ == 0 {
                    return v___x_4817_;
                } else {
                    let mut v___x_4821_: usize = 0;
                    let mut v___x_4822_: usize = 0;
                    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4821_ = 0usize;
                    v___x_4822_ = lean_usize_of_nat(v___x_4818_);
                    v___x_4823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_4783_, v_tail_4816_, v___x_4821_, v___x_4822_, v___x_4817_);
                    return v___x_4823_;
                }
            } else {
                let mut v___x_4824_: usize = 0;
                let mut v___x_4825_: usize = 0;
                let mut v___x_4826_: *mut LeanObject = core::ptr::null_mut();
                v___x_4824_ = 0usize;
                v___x_4825_ = lean_usize_of_nat(v___x_4818_);
                v___x_4826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_4783_, v_tail_4816_, v___x_4824_, v___x_4825_, v___x_4817_);
                return v___x_4826_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0___boxed(
    mut v___x_4827_: *mut LeanObject,
    mut v_t_4828_: *mut LeanObject,
    mut v_init_4829_: *mut LeanObject,
    mut v_start_4830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4831_: *mut LeanObject = core::ptr::null_mut();
    v_res_4831_ =
        l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(
            v___x_4827_,
            v_t_4828_,
            v_init_4829_,
            v_start_4830_,
        );
    lean_dec(v_start_4830_);
    lean_dec_ref(v_t_4828_);
    lean_dec_ref(v___x_4827_);
    return v_res_4831_;
}
pub unsafe fn _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0()
-> *mut LeanObject {
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    v___x_4832_ = lean_unsigned_to_nat(32);
    v___x_4833_ = lean_mk_empty_array_with_capacity(v___x_4832_);
    v___x_4834_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4834_, 0, v___x_4833_);
    return v___x_4834_;
}
pub unsafe fn _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1()
-> *mut LeanObject {
    let mut v___x_4835_: usize = 0;
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    v___x_4835_ = 5usize;
    v___x_4836_ = lean_unsigned_to_nat(0);
    v___x_4837_ = lean_unsigned_to_nat(32);
    v___x_4838_ = lean_mk_empty_array_with_capacity(v___x_4837_);
    v___x_4839_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0_once), _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0);
    v___x_4840_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_4840_, 0, v___x_4839_);
    lean_ctor_set(v___x_4840_, 1, v___x_4838_);
    lean_ctor_set(v___x_4840_, 2, v___x_4836_);
    lean_ctor_set(v___x_4840_, 3, v___x_4836_);
    lean_ctor_set_usize(v___x_4840_, 4, v___x_4835_);
    return v___x_4840_;
}
pub unsafe fn l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(
    mut v___x_4841_: *mut LeanObject,
    mut v_x_4842_: *mut LeanObject,
    mut v_x_4843_: usize,
    mut v_x_4844_: usize,
) -> *mut LeanObject {
    let mut v_cs_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_4846_: usize = 0;
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: u8 = 0;
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4852_: u8 = 0;
    let mut v___x_4853_: usize = 0;
    let mut v___x_4854_: usize = 0;
    let mut v___x_4855_: usize = 0;
    let mut v_i_4856_: usize = 0;
    let mut v___x_4857_: usize = 0;
    let mut v_shift_4858_: usize = 0;
    let mut v_v_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4867_: u8 = 0;
    let mut v_unused_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: u8 = 0;
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4875_: u8 = 0;
    let mut v_v_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4886_: u8 = 0;
    let mut v_unused_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4842_) == 0 {
                    v_cs_4845_ = lean_ctor_get(v_x_4842_, 0);
                    v_j_4846_ = lean_usize_shift_right(v_x_4843_, v_x_4844_);
                    v___x_4847_ = lean_usize_to_nat(v_j_4846_);
                    v___x_4848_ = lean_array_get_size(v_cs_4845_);
                    v___x_4849_ = lean_nat_dec_lt(v___x_4847_, v___x_4848_);
                    if v___x_4849_ == 0 {
                        lean_dec(v___x_4847_);
                        return v_x_4842_;
                    } else {
                        lean_inc_ref(v_cs_4845_);
                        v_isSharedCheck_4867_ = (!lean_is_exclusive(v_x_4842_)) as u8;
                        if v_isSharedCheck_4867_ == 0 {
                            v_unused_4868_ = lean_ctor_get(v_x_4842_, 0);
                            lean_dec(v_unused_4868_);
                            v___x_4851_ = v_x_4842_;
                            v_isShared_4852_ = v_isSharedCheck_4867_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_4842_);
                            v___x_4851_ = lean_box(0);
                            v_isShared_4852_ = v_isSharedCheck_4867_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_vs_4869_ = lean_ctor_get(v_x_4842_, 0);
                    v___x_4870_ = lean_usize_to_nat(v_x_4843_);
                    v___x_4871_ = lean_array_get_size(v_vs_4869_);
                    v___x_4872_ = lean_nat_dec_lt(v___x_4870_, v___x_4871_);
                    if v___x_4872_ == 0 {
                        lean_dec(v___x_4870_);
                        return v_x_4842_;
                    } else {
                        lean_inc_ref(v_vs_4869_);
                        v_isSharedCheck_4886_ = (!lean_is_exclusive(v_x_4842_)) as u8;
                        if v_isSharedCheck_4886_ == 0 {
                            v_unused_4887_ = lean_ctor_get(v_x_4842_, 0);
                            lean_dec(v_unused_4887_);
                            v___x_4874_ = v_x_4842_;
                            v_isShared_4875_ = v_isSharedCheck_4886_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v_x_4842_);
                            v___x_4874_ = lean_box(0);
                            v_isShared_4875_ = v_isSharedCheck_4886_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4853_ = 1usize;
                v___x_4854_ = lean_usize_shift_left(v___x_4853_, v_x_4844_);
                v___x_4855_ = lean_usize_sub(v___x_4854_, v___x_4853_);
                v_i_4856_ = lean_usize_land(v_x_4843_, v___x_4855_);
                v___x_4857_ = 5usize;
                v_shift_4858_ = lean_usize_sub(v_x_4844_, v___x_4857_);
                v_v_4859_ = lean_array_fget(v_cs_4845_, v___x_4847_);
                v___x_4860_ = lean_box(0);
                v_xs_x27_4861_ = lean_array_fset(v_cs_4845_, v___x_4847_, v___x_4860_);
                v___x_4862_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v___x_4841_, v_v_4859_, v_i_4856_, v_shift_4858_);
                v___x_4863_ = lean_array_fset(v_xs_x27_4861_, v___x_4847_, v___x_4862_);
                lean_dec(v___x_4847_);
                if v_isShared_4852_ == 0 {
                    lean_ctor_set(v___x_4851_, 0, v___x_4863_);
                    v___x_4865_ = v___x_4851_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4866_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4866_, 0, v___x_4863_);
                    v___x_4865_ = v_reuseFailAlloc_4866_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4865_;
            }
            3 => {
                v_v_4876_ = lean_array_fget(v_vs_4869_, v___x_4870_);
                v___x_4877_ = lean_box(0);
                v_xs_x27_4878_ = lean_array_fset(v_vs_4869_, v___x_4870_, v___x_4877_);
                v___x_4879_ = lean_unsigned_to_nat(0);
                v___x_4880_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once), _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1);
                v___x_4881_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_4841_, v_v_4876_, v___x_4880_, v___x_4879_);
                lean_dec(v_v_4876_);
                v___x_4882_ = lean_array_fset(v_xs_x27_4878_, v___x_4870_, v___x_4881_);
                lean_dec(v___x_4870_);
                if v_isShared_4875_ == 0 {
                    lean_ctor_set(v___x_4874_, 0, v___x_4882_);
                    v___x_4884_ = v___x_4874_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4885_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4885_, 0, v___x_4882_);
                    v___x_4884_ = v_reuseFailAlloc_4885_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4884_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___boxed(
    mut v___x_4888_: *mut LeanObject,
    mut v_x_4889_: *mut LeanObject,
    mut v_x_4890_: *mut LeanObject,
    mut v_x_4891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2238__boxed_4892_: usize = 0;
    let mut v_x_2239__boxed_4893_: usize = 0;
    let mut v_res_4894_: *mut LeanObject = core::ptr::null_mut();
    v_x_2238__boxed_4892_ = lean_unbox_usize(v_x_4890_);
    lean_dec(v_x_4890_);
    v_x_2239__boxed_4893_ = lean_unbox_usize(v_x_4891_);
    lean_dec(v_x_4891_);
    v_res_4894_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v___x_4888_, v_x_4889_, v_x_2238__boxed_4892_, v_x_2239__boxed_4893_);
    lean_dec_ref(v___x_4888_);
    return v_res_4894_;
}
pub unsafe fn l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(
    mut v___x_4895_: *mut LeanObject,
    mut v_t_4896_: *mut LeanObject,
    mut v_i_4897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_4901_: usize = 0;
    let mut v_tailOff_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4905_: u8 = 0;
    let mut v___x_4906_: u8 = 0;
    let mut v___x_4907_: usize = 0;
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: u8 = 0;
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_4898_ = lean_ctor_get(v_t_4896_, 0);
                v_tail_4899_ = lean_ctor_get(v_t_4896_, 1);
                v_size_4900_ = lean_ctor_get(v_t_4896_, 2);
                v_shift_4901_ = lean_ctor_get_usize(v_t_4896_, 4);
                v_tailOff_4902_ = lean_ctor_get(v_t_4896_, 3);
                v_isSharedCheck_4930_ = (!lean_is_exclusive(v_t_4896_)) as u8;
                if v_isSharedCheck_4930_ == 0 {
                    v___x_4904_ = v_t_4896_;
                    v_isShared_4905_ = v_isSharedCheck_4930_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_tailOff_4902_);
                    lean_inc(v_size_4900_);
                    lean_inc(v_tail_4899_);
                    lean_inc(v_root_4898_);
                    lean_dec(v_t_4896_);
                    v___x_4904_ = lean_box(0);
                    v_isShared_4905_ = v_isSharedCheck_4930_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4906_ = lean_nat_dec_le(v_tailOff_4902_, v_i_4897_);
                if v___x_4906_ == 0 {
                    v___x_4907_ = lean_usize_of_nat(v_i_4897_);
                    v___x_4908_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v___x_4895_, v_root_4898_, v___x_4907_, v_shift_4901_);
                    if v_isShared_4905_ == 0 {
                        lean_ctor_set(v___x_4904_, 0, v___x_4908_);
                        v___x_4910_ = v___x_4904_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4911_ =
                            lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4911_, 0, v___x_4908_);
                        lean_ctor_set(v_reuseFailAlloc_4911_, 1, v_tail_4899_);
                        lean_ctor_set(v_reuseFailAlloc_4911_, 2, v_size_4900_);
                        lean_ctor_set(v_reuseFailAlloc_4911_, 3, v_tailOff_4902_);
                        lean_ctor_set_usize(v_reuseFailAlloc_4911_, 4, v_shift_4901_);
                        v___x_4910_ = v_reuseFailAlloc_4911_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4912_ = lean_nat_sub(v_i_4897_, v_tailOff_4902_);
                    v___x_4913_ = lean_array_get_size(v_tail_4899_);
                    v___x_4914_ = lean_nat_dec_lt(v___x_4912_, v___x_4913_);
                    if v___x_4914_ == 0 {
                        lean_dec(v___x_4912_);
                        if v_isShared_4905_ == 0 {
                            v___x_4916_ = v___x_4904_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4917_ =
                                lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_root_4898_);
                            lean_ctor_set(v_reuseFailAlloc_4917_, 1, v_tail_4899_);
                            lean_ctor_set(v_reuseFailAlloc_4917_, 2, v_size_4900_);
                            lean_ctor_set(v_reuseFailAlloc_4917_, 3, v_tailOff_4902_);
                            lean_ctor_set_usize(v_reuseFailAlloc_4917_, 4, v_shift_4901_);
                            v___x_4916_ = v_reuseFailAlloc_4917_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_v_4918_ = lean_array_fget(v_tail_4899_, v___x_4912_);
                        v___x_4919_ = lean_box(0);
                        v_xs_x27_4920_ = lean_array_fset(v_tail_4899_, v___x_4912_, v___x_4919_);
                        v___x_4921_ = lean_unsigned_to_nat(32);
                        v___x_4922_ = lean_mk_empty_array_with_capacity(v___x_4921_);
                        lean_dec_ref(v___x_4922_);
                        v___x_4923_ = lean_unsigned_to_nat(0);
                        v___x_4924_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once), _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1);
                        v___x_4925_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_4895_, v_v_4918_, v___x_4924_, v___x_4923_);
                        lean_dec(v_v_4918_);
                        v___x_4926_ = lean_array_fset(v_xs_x27_4920_, v___x_4912_, v___x_4925_);
                        lean_dec(v___x_4912_);
                        if v_isShared_4905_ == 0 {
                            lean_ctor_set(v___x_4904_, 1, v___x_4926_);
                            v___x_4928_ = v___x_4904_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4929_ =
                                lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_root_4898_);
                            lean_ctor_set(v_reuseFailAlloc_4929_, 1, v___x_4926_);
                            lean_ctor_set(v_reuseFailAlloc_4929_, 2, v_size_4900_);
                            lean_ctor_set(v_reuseFailAlloc_4929_, 3, v_tailOff_4902_);
                            lean_ctor_set_usize(v_reuseFailAlloc_4929_, 4, v_shift_4901_);
                            v___x_4928_ = v_reuseFailAlloc_4929_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4910_;
            }
            3 => {
                return v___x_4916_;
            }
            4 => {
                return v___x_4928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1___boxed(
    mut v___x_4931_: *mut LeanObject,
    mut v_t_4932_: *mut LeanObject,
    mut v_i_4933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4934_: *mut LeanObject = core::ptr::null_mut();
    v_res_4934_ =
        l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(
            v___x_4931_,
            v_t_4932_,
            v_i_4933_,
        );
    lean_dec(v_i_4933_);
    lean_dec_ref(v___x_4931_);
    return v_res_4934_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(
    mut v_p_4935_: *mut LeanObject,
    mut v_v_4936_: *mut LeanObject,
    mut v_s_4937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vars_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_x27_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_x27_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natDef_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dvds_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowers_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uppers_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_occurs_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextCnstrId_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_4953_: u8 = 0;
    let mut v_conflict_x3f_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_divMod_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntIds_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntInfos_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedCommRing_4961_: u8 = 0;
    let mut v_nonlinearOccs_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4965_: u8 = 0;
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4970_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_4938_ = lean_ctor_get(v_s_4937_, 0);
                v_varMap_4939_ = lean_ctor_get(v_s_4937_, 1);
                v_vars_x27_4940_ = lean_ctor_get(v_s_4937_, 2);
                v_varMap_x27_4941_ = lean_ctor_get(v_s_4937_, 3);
                v_natToIntMap_4942_ = lean_ctor_get(v_s_4937_, 4);
                v_natDef_4943_ = lean_ctor_get(v_s_4937_, 5);
                v_dvds_4944_ = lean_ctor_get(v_s_4937_, 6);
                v_lowers_4945_ = lean_ctor_get(v_s_4937_, 7);
                v_uppers_4946_ = lean_ctor_get(v_s_4937_, 8);
                v_diseqs_4947_ = lean_ctor_get(v_s_4937_, 9);
                v_elimEqs_4948_ = lean_ctor_get(v_s_4937_, 10);
                v_elimStack_4949_ = lean_ctor_get(v_s_4937_, 11);
                v_occurs_4950_ = lean_ctor_get(v_s_4937_, 12);
                v_assignment_4951_ = lean_ctor_get(v_s_4937_, 13);
                v_nextCnstrId_4952_ = lean_ctor_get(v_s_4937_, 14);
                v_caseSplits_4953_ = lean_ctor_get_uint8(
                    v_s_4937_,
                    (core::mem::size_of::<*mut LeanObject>() * 23) as u32,
                );
                v_conflict_x3f_4954_ = lean_ctor_get(v_s_4937_, 15);
                v_diseqSplits_4955_ = lean_ctor_get(v_s_4937_, 16);
                v_divMod_4956_ = lean_ctor_get(v_s_4937_, 17);
                v_toIntIds_4957_ = lean_ctor_get(v_s_4937_, 18);
                v_toIntInfos_4958_ = lean_ctor_get(v_s_4937_, 19);
                v_toIntTermMap_4959_ = lean_ctor_get(v_s_4937_, 20);
                v_toIntVarMap_4960_ = lean_ctor_get(v_s_4937_, 21);
                v_usedCommRing_4961_ = lean_ctor_get_uint8(
                    v_s_4937_,
                    (core::mem::size_of::<*mut LeanObject>() * 23 + 1) as u32,
                );
                v_nonlinearOccs_4962_ = lean_ctor_get(v_s_4937_, 22);
                v_isSharedCheck_4970_ = (!lean_is_exclusive(v_s_4937_)) as u8;
                if v_isSharedCheck_4970_ == 0 {
                    v___x_4964_ = v_s_4937_;
                    v_isShared_4965_ = v_isSharedCheck_4970_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nonlinearOccs_4962_);
                    lean_inc(v_toIntVarMap_4960_);
                    lean_inc(v_toIntTermMap_4959_);
                    lean_inc(v_toIntInfos_4958_);
                    lean_inc(v_toIntIds_4957_);
                    lean_inc(v_divMod_4956_);
                    lean_inc(v_diseqSplits_4955_);
                    lean_inc(v_conflict_x3f_4954_);
                    lean_inc(v_nextCnstrId_4952_);
                    lean_inc(v_assignment_4951_);
                    lean_inc(v_occurs_4950_);
                    lean_inc(v_elimStack_4949_);
                    lean_inc(v_elimEqs_4948_);
                    lean_inc(v_diseqs_4947_);
                    lean_inc(v_uppers_4946_);
                    lean_inc(v_lowers_4945_);
                    lean_inc(v_dvds_4944_);
                    lean_inc(v_natDef_4943_);
                    lean_inc(v_natToIntMap_4942_);
                    lean_inc(v_varMap_x27_4941_);
                    lean_inc(v_vars_x27_4940_);
                    lean_inc(v_varMap_4939_);
                    lean_inc(v_vars_4938_);
                    lean_dec(v_s_4937_);
                    v___x_4964_ = lean_box(0);
                    v_isShared_4965_ = v_isSharedCheck_4970_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4966_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_p_4935_, v_uppers_4946_, v_v_4936_);
                if v_isShared_4965_ == 0 {
                    lean_ctor_set(v___x_4964_, 8, v___x_4966_);
                    v___x_4968_ = v___x_4964_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4969_ = lean_alloc_ctor(0, 23, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 0, v_vars_4938_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 1, v_varMap_4939_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 2, v_vars_x27_4940_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 3, v_varMap_x27_4941_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 4, v_natToIntMap_4942_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 5, v_natDef_4943_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 6, v_dvds_4944_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 7, v_lowers_4945_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 8, v___x_4966_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 9, v_diseqs_4947_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 10, v_elimEqs_4948_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 11, v_elimStack_4949_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 12, v_occurs_4950_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 13, v_assignment_4951_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 14, v_nextCnstrId_4952_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 15, v_conflict_x3f_4954_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 16, v_diseqSplits_4955_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 17, v_divMod_4956_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 18, v_toIntIds_4957_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 19, v_toIntInfos_4958_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 20, v_toIntTermMap_4959_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 21, v_toIntVarMap_4960_);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 22, v_nonlinearOccs_4962_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4969_,
                        (core::mem::size_of::<*mut LeanObject>() * 23) as u32,
                        v_caseSplits_4953_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4969_,
                        (core::mem::size_of::<*mut LeanObject>() * 23 + 1) as u32,
                        v_usedCommRing_4961_,
                    );
                    v___x_4968_ = v_reuseFailAlloc_4969_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4968_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed(
    mut v_p_4971_: *mut LeanObject,
    mut v_v_4972_: *mut LeanObject,
    mut v_s_4973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4974_: *mut LeanObject = core::ptr::null_mut();
    v_res_4974_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(
        v_p_4971_, v_v_4972_, v_s_4973_,
    );
    lean_dec(v_v_4972_);
    lean_dec_ref(v_p_4971_);
    return v_res_4974_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(
    mut v_p_4975_: *mut LeanObject,
    mut v_v_4976_: *mut LeanObject,
    mut v_s_4977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vars_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_x27_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_x27_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natDef_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dvds_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowers_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uppers_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_occurs_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextCnstrId_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_4993_: u8 = 0;
    let mut v_conflict_x3f_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_divMod_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntIds_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntInfos_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedCommRing_5001_: u8 = 0;
    let mut v_nonlinearOccs_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5005_: u8 = 0;
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5010_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_4978_ = lean_ctor_get(v_s_4977_, 0);
                v_varMap_4979_ = lean_ctor_get(v_s_4977_, 1);
                v_vars_x27_4980_ = lean_ctor_get(v_s_4977_, 2);
                v_varMap_x27_4981_ = lean_ctor_get(v_s_4977_, 3);
                v_natToIntMap_4982_ = lean_ctor_get(v_s_4977_, 4);
                v_natDef_4983_ = lean_ctor_get(v_s_4977_, 5);
                v_dvds_4984_ = lean_ctor_get(v_s_4977_, 6);
                v_lowers_4985_ = lean_ctor_get(v_s_4977_, 7);
                v_uppers_4986_ = lean_ctor_get(v_s_4977_, 8);
                v_diseqs_4987_ = lean_ctor_get(v_s_4977_, 9);
                v_elimEqs_4988_ = lean_ctor_get(v_s_4977_, 10);
                v_elimStack_4989_ = lean_ctor_get(v_s_4977_, 11);
                v_occurs_4990_ = lean_ctor_get(v_s_4977_, 12);
                v_assignment_4991_ = lean_ctor_get(v_s_4977_, 13);
                v_nextCnstrId_4992_ = lean_ctor_get(v_s_4977_, 14);
                v_caseSplits_4993_ = lean_ctor_get_uint8(
                    v_s_4977_,
                    (core::mem::size_of::<*mut LeanObject>() * 23) as u32,
                );
                v_conflict_x3f_4994_ = lean_ctor_get(v_s_4977_, 15);
                v_diseqSplits_4995_ = lean_ctor_get(v_s_4977_, 16);
                v_divMod_4996_ = lean_ctor_get(v_s_4977_, 17);
                v_toIntIds_4997_ = lean_ctor_get(v_s_4977_, 18);
                v_toIntInfos_4998_ = lean_ctor_get(v_s_4977_, 19);
                v_toIntTermMap_4999_ = lean_ctor_get(v_s_4977_, 20);
                v_toIntVarMap_5000_ = lean_ctor_get(v_s_4977_, 21);
                v_usedCommRing_5001_ = lean_ctor_get_uint8(
                    v_s_4977_,
                    (core::mem::size_of::<*mut LeanObject>() * 23 + 1) as u32,
                );
                v_nonlinearOccs_5002_ = lean_ctor_get(v_s_4977_, 22);
                v_isSharedCheck_5010_ = (!lean_is_exclusive(v_s_4977_)) as u8;
                if v_isSharedCheck_5010_ == 0 {
                    v___x_5004_ = v_s_4977_;
                    v_isShared_5005_ = v_isSharedCheck_5010_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nonlinearOccs_5002_);
                    lean_inc(v_toIntVarMap_5000_);
                    lean_inc(v_toIntTermMap_4999_);
                    lean_inc(v_toIntInfos_4998_);
                    lean_inc(v_toIntIds_4997_);
                    lean_inc(v_divMod_4996_);
                    lean_inc(v_diseqSplits_4995_);
                    lean_inc(v_conflict_x3f_4994_);
                    lean_inc(v_nextCnstrId_4992_);
                    lean_inc(v_assignment_4991_);
                    lean_inc(v_occurs_4990_);
                    lean_inc(v_elimStack_4989_);
                    lean_inc(v_elimEqs_4988_);
                    lean_inc(v_diseqs_4987_);
                    lean_inc(v_uppers_4986_);
                    lean_inc(v_lowers_4985_);
                    lean_inc(v_dvds_4984_);
                    lean_inc(v_natDef_4983_);
                    lean_inc(v_natToIntMap_4982_);
                    lean_inc(v_varMap_x27_4981_);
                    lean_inc(v_vars_x27_4980_);
                    lean_inc(v_varMap_4979_);
                    lean_inc(v_vars_4978_);
                    lean_dec(v_s_4977_);
                    v___x_5004_ = lean_box(0);
                    v_isShared_5005_ = v_isSharedCheck_5010_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5006_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_p_4975_, v_lowers_4985_, v_v_4976_);
                if v_isShared_5005_ == 0 {
                    lean_ctor_set(v___x_5004_, 7, v___x_5006_);
                    v___x_5008_ = v___x_5004_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5009_ = lean_alloc_ctor(0, 23, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_vars_4978_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 1, v_varMap_4979_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 2, v_vars_x27_4980_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 3, v_varMap_x27_4981_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 4, v_natToIntMap_4982_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 5, v_natDef_4983_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 6, v_dvds_4984_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 7, v___x_5006_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 8, v_uppers_4986_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 9, v_diseqs_4987_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 10, v_elimEqs_4988_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 11, v_elimStack_4989_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 12, v_occurs_4990_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 13, v_assignment_4991_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 14, v_nextCnstrId_4992_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 15, v_conflict_x3f_4994_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 16, v_diseqSplits_4995_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 17, v_divMod_4996_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 18, v_toIntIds_4997_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 19, v_toIntInfos_4998_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 20, v_toIntTermMap_4999_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 21, v_toIntVarMap_5000_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 22, v_nonlinearOccs_5002_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5009_,
                        (core::mem::size_of::<*mut LeanObject>() * 23) as u32,
                        v_caseSplits_4993_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5009_,
                        (core::mem::size_of::<*mut LeanObject>() * 23 + 1) as u32,
                        v_usedCommRing_5001_,
                    );
                    v___x_5008_ = v_reuseFailAlloc_5009_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5008_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed(
    mut v_p_5011_: *mut LeanObject,
    mut v_v_5012_: *mut LeanObject,
    mut v_s_5013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5014_: *mut LeanObject = core::ptr::null_mut();
    v_res_5014_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(
        v_p_5011_, v_v_5012_, v_s_5013_,
    );
    lean_dec(v_v_5012_);
    lean_dec_ref(v_p_5011_);
    return v_res_5014_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(
    mut v_c_5015_: *mut LeanObject,
    mut v_a_5016_: *mut LeanObject,
    mut v_a_5017_: *mut LeanObject,
    mut v_a_5018_: *mut LeanObject,
    mut v_a_5019_: *mut LeanObject,
    mut v_a_5020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_5022_: *mut LeanObject = core::ptr::null_mut();
    v_p_5022_ = lean_ctor_get(v_c_5015_, 0);
    if lean_obj_tag(v_p_5022_) == 1 {
        let mut v_k_5023_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5024_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5026_: u8 = 0;
        lean_inc_ref(v_p_5022_);
        lean_dec_ref(v_c_5015_);
        v_k_5023_ = lean_ctor_get(v_p_5022_, 0);
        v_v_5024_ = lean_ctor_get(v_p_5022_, 1);
        lean_inc(v_v_5024_);
        v___x_5025_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once
            ),
            _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9,
        );
        v___x_5026_ = lean_int_dec_lt(v_k_5023_, v___x_5025_);
        if v___x_5026_ == 0 {
            let mut v___f_5027_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
            v___f_5027_ = lean_alloc_closure(
                l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed
                    as *mut core::ffi::c_void,
                3,
                2,
            );
            lean_closure_set(v___f_5027_, 0, v_p_5022_);
            lean_closure_set(v___f_5027_, 1, v_v_5024_);
            v___x_5028_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
            v___x_5029_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_5028_, v___f_5027_, v_a_5016_);
            return v___x_5029_;
        } else {
            let mut v___f_5030_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
            v___f_5030_ = lean_alloc_closure(
                l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed
                    as *mut core::ffi::c_void,
                3,
                2,
            );
            lean_closure_set(v___f_5030_, 0, v_p_5022_);
            lean_closure_set(v___f_5030_, 1, v_v_5024_);
            v___x_5031_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
            v___x_5032_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_5031_, v___f_5030_, v_a_5016_);
            return v___x_5032_;
        }
    } else {
        let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
        v___x_5033_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(
            v_c_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_,
        );
        return v___x_5033_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___boxed(
    mut v_c_5034_: *mut LeanObject,
    mut v_a_5035_: *mut LeanObject,
    mut v_a_5036_: *mut LeanObject,
    mut v_a_5037_: *mut LeanObject,
    mut v_a_5038_: *mut LeanObject,
    mut v_a_5039_: *mut LeanObject,
    mut v_a_5040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5041_: *mut LeanObject = core::ptr::null_mut();
    v_res_5041_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(
        v_c_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_,
    );
    lean_dec(v_a_5039_);
    lean_dec_ref(v_a_5038_);
    lean_dec(v_a_5037_);
    lean_dec_ref(v_a_5036_);
    lean_dec(v_a_5035_);
    return v_res_5041_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(
    mut v_c_5042_: *mut LeanObject,
    mut v_a_5043_: *mut LeanObject,
    mut v_a_5044_: *mut LeanObject,
    mut v_a_5045_: *mut LeanObject,
    mut v_a_5046_: *mut LeanObject,
    mut v_a_5047_: *mut LeanObject,
    mut v_a_5048_: *mut LeanObject,
    mut v_a_5049_: *mut LeanObject,
    mut v_a_5050_: *mut LeanObject,
    mut v_a_5051_: *mut LeanObject,
    mut v_a_5052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5054_: *mut LeanObject = core::ptr::null_mut();
    v___x_5054_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(
        v_c_5042_, v_a_5043_, v_a_5049_, v_a_5050_, v_a_5051_, v_a_5052_,
    );
    return v___x_5054_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___boxed(
    mut v_c_5055_: *mut LeanObject,
    mut v_a_5056_: *mut LeanObject,
    mut v_a_5057_: *mut LeanObject,
    mut v_a_5058_: *mut LeanObject,
    mut v_a_5059_: *mut LeanObject,
    mut v_a_5060_: *mut LeanObject,
    mut v_a_5061_: *mut LeanObject,
    mut v_a_5062_: *mut LeanObject,
    mut v_a_5063_: *mut LeanObject,
    mut v_a_5064_: *mut LeanObject,
    mut v_a_5065_: *mut LeanObject,
    mut v_a_5066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5067_: *mut LeanObject = core::ptr::null_mut();
    v_res_5067_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(
        v_c_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_,
        v_a_5063_, v_a_5064_, v_a_5065_,
    );
    lean_dec(v_a_5065_);
    lean_dec_ref(v_a_5064_);
    lean_dec(v_a_5063_);
    lean_dec_ref(v_a_5062_);
    lean_dec(v_a_5061_);
    lean_dec_ref(v_a_5060_);
    lean_dec(v_a_5059_);
    lean_dec_ref(v_a_5058_);
    lean_dec(v_a_5057_);
    lean_dec(v_a_5056_);
    return v_res_5067_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5()
-> *mut LeanObject {
    let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut LeanObject = core::ptr::null_mut();
    v___x_5081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4;
    v___x_5082_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5;
    v___x_5083_ = l_Lean_Name_append(v___x_5082_, v___x_5081_);
    return v___x_5083_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7()
-> *mut LeanObject {
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut LeanObject = core::ptr::null_mut();
    v___x_5085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6;
    v___x_5086_ = l_Lean_stringToMessageData(v___x_5085_);
    return v___x_5086_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(
    mut v___x_5087_: *mut LeanObject,
    mut v_c_5088_: *mut LeanObject,
    mut v_as_5089_: *mut LeanObject,
    mut v_sz_5090_: usize,
    mut v_i_5091_: usize,
    mut v_b_5092_: *mut LeanObject,
    mut v___y_5093_: *mut LeanObject,
    mut v___y_5094_: *mut LeanObject,
    mut v___y_5095_: *mut LeanObject,
    mut v___y_5096_: *mut LeanObject,
    mut v___y_5097_: *mut LeanObject,
    mut v___y_5098_: *mut LeanObject,
    mut v___y_5099_: *mut LeanObject,
    mut v___y_5100_: *mut LeanObject,
    mut v___y_5101_: *mut LeanObject,
    mut v___y_5102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5104_: u8 = 0;
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5109_: u8 = 0;
    let mut v_a_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: u8 = 0;
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: usize = 0;
    let mut v___x_5116_: usize = 0;
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5121_: u8 = 0;
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5138_: u8 = 0;
    let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5150_: u8 = 0;
    let mut v_unused_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5155_: u8 = 0;
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5159_: u8 = 0;
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: u8 = 0;
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5171_: u8 = 0;
    let mut v___x_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5175_: u8 = 0;
    let mut v_a_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5179_: u8 = 0;
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5183_: u8 = 0;
    let mut v_a_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5187_: u8 = 0;
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5191_: u8 = 0;
    let mut v_isSharedCheck_5192_: u8 = 0;
    let mut v_unused_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5104_ = lean_usize_dec_lt(v_i_5091_, v_sz_5090_);
                if v___x_5104_ == 0 {
                    lean_dec_ref(v_c_5088_);
                    lean_dec_ref(v___x_5087_);
                    v___x_5105_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5105_, 0, v_b_5092_);
                    return v___x_5105_;
                } else {
                    v_snd_5106_ = lean_ctor_get(v_b_5092_, 1);
                    v_isSharedCheck_5192_ = (!lean_is_exclusive(v_b_5092_)) as u8;
                    if v_isSharedCheck_5192_ == 0 {
                        v_unused_5193_ = lean_ctor_get(v_b_5092_, 0);
                        lean_dec(v_unused_5193_);
                        v___x_5108_ = v_b_5092_;
                        v_isShared_5109_ = v_isSharedCheck_5192_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5106_);
                        lean_dec(v_b_5092_);
                        v___x_5108_ = lean_box(0);
                        v_isShared_5109_ = v_isSharedCheck_5192_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5110_ = lean_array_uget_borrowed(v_as_5089_, v_i_5091_);
                v_p_5111_ = lean_ctor_get(v_a_5110_, 0);
                v___x_5112_ = lean_box(0);
                v___x_5113_ = l_Int_Linear_Poly_isNegEq(v___x_5087_, v_p_5111_);
                if v___x_5113_ == 0 {
                    lean_del_object(v___x_5108_);
                    lean_dec(v_snd_5106_);
                    v___x_5114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__1;
                    v___x_5115_ = 1usize;
                    v___x_5116_ = lean_usize_add(v_i_5091_, v___x_5115_);
                    v_i_5091_ = v___x_5116_;
                    v_b_5092_ = v___x_5114_;
                    state = 0;
                    continue;
                } else {
                    lean_inc(v_a_5110_);
                    v___x_5118_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(
                        v_a_5110_,
                        v___y_5093_,
                        v___y_5099_,
                        v___y_5100_,
                        v___y_5101_,
                        v___y_5102_,
                    );
                    if lean_obj_tag(v___x_5118_) == 0 {
                        lean_dec_ref_known(v___x_5118_, 1);
                        v_options_5119_ = lean_ctor_get(v___y_5101_, 2);
                        v_inheritedTraceOptions_5120_ = lean_ctor_get(v___y_5101_, 13);
                        v_hasTrace_5121_ = lean_ctor_get_uint8(
                            v_options_5119_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        lean_inc(v_a_5110_);
                        v___x_5122_ = lean_alloc_ctor(8, 2, (0) as u32);
                        lean_ctor_set(v___x_5122_, 0, v_c_5088_);
                        lean_ctor_set(v___x_5122_, 1, v_a_5110_);
                        v___x_5123_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5123_, 0, v___x_5087_);
                        lean_ctor_set(v___x_5123_, 1, v___x_5122_);
                        if v_hasTrace_5121_ == 0 {
                            v___y_5125_ = v___y_5093_;
                            v___y_5126_ = v___y_5094_;
                            v___y_5127_ = v___y_5095_;
                            v___y_5128_ = v___y_5096_;
                            v___y_5129_ = v___y_5097_;
                            v___y_5130_ = v___y_5098_;
                            v___y_5131_ = v___y_5099_;
                            v___y_5132_ = v___y_5100_;
                            v___y_5133_ = v___y_5101_;
                            v___y_5134_ = v___y_5102_;
                            state = 2;
                            continue;
                        } else {
                            v___x_5160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4;
                            v___x_5161_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
                            v___x_5162_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_5120_,
                                v_options_5119_,
                                v___x_5161_,
                            );
                            if v___x_5162_ == 0 {
                                v___y_5125_ = v___y_5093_;
                                v___y_5126_ = v___y_5094_;
                                v___y_5127_ = v___y_5095_;
                                v___y_5128_ = v___y_5096_;
                                v___y_5129_ = v___y_5097_;
                                v___y_5130_ = v___y_5098_;
                                v___y_5131_ = v___y_5099_;
                                v___y_5132_ = v___y_5100_;
                                v___y_5133_ = v___y_5101_;
                                v___y_5134_ = v___y_5102_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc_ref(v___x_5123_);
                                v___x_5163_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(
                                    v___x_5123_,
                                    v___y_5093_,
                                    v___y_5101_,
                                );
                                if lean_obj_tag(v___x_5163_) == 0 {
                                    v_a_5164_ = lean_ctor_get(v___x_5163_, 0);
                                    lean_inc(v_a_5164_);
                                    lean_dec_ref_known(v___x_5163_, 1);
                                    v___x_5165_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
                                    v___x_5166_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_5166_, 0, v___x_5165_);
                                    lean_ctor_set(v___x_5166_, 1, v_a_5164_);
                                    v___x_5167_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_5160_, v___x_5166_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_);
                                    if lean_obj_tag(v___x_5167_) == 0 {
                                        lean_dec_ref_known(v___x_5167_, 1);
                                        v___y_5125_ = v___y_5093_;
                                        v___y_5126_ = v___y_5094_;
                                        v___y_5127_ = v___y_5095_;
                                        v___y_5128_ = v___y_5096_;
                                        v___y_5129_ = v___y_5097_;
                                        v___y_5130_ = v___y_5098_;
                                        v___y_5131_ = v___y_5099_;
                                        v___y_5132_ = v___y_5100_;
                                        v___y_5133_ = v___y_5101_;
                                        v___y_5134_ = v___y_5102_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec_ref_known(v___x_5123_, 2);
                                        lean_del_object(v___x_5108_);
                                        lean_dec(v_snd_5106_);
                                        v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
                                        v_isSharedCheck_5175_ =
                                            (!lean_is_exclusive(v___x_5167_)) as u8;
                                        if v_isSharedCheck_5175_ == 0 {
                                            v___x_5170_ = v___x_5167_;
                                            v_isShared_5171_ = v_isSharedCheck_5175_;
                                            state = 8;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5168_);
                                            lean_dec(v___x_5167_);
                                            v___x_5170_ = lean_box(0);
                                            v_isShared_5171_ = v_isSharedCheck_5175_;
                                            state = 8;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref_known(v___x_5123_, 2);
                                    lean_del_object(v___x_5108_);
                                    lean_dec(v_snd_5106_);
                                    v_a_5176_ = lean_ctor_get(v___x_5163_, 0);
                                    v_isSharedCheck_5183_ = (!lean_is_exclusive(v___x_5163_)) as u8;
                                    if v_isSharedCheck_5183_ == 0 {
                                        v___x_5178_ = v___x_5163_;
                                        v_isShared_5179_ = v_isSharedCheck_5183_;
                                        state = 10;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5176_);
                                        lean_dec(v___x_5163_);
                                        v___x_5178_ = lean_box(0);
                                        v_isShared_5179_ = v_isSharedCheck_5183_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_5108_);
                        lean_dec(v_snd_5106_);
                        lean_dec_ref(v_c_5088_);
                        lean_dec_ref(v___x_5087_);
                        v_a_5184_ = lean_ctor_get(v___x_5118_, 0);
                        v_isSharedCheck_5191_ = (!lean_is_exclusive(v___x_5118_)) as u8;
                        if v_isSharedCheck_5191_ == 0 {
                            v___x_5186_ = v___x_5118_;
                            v_isShared_5187_ = v_isSharedCheck_5191_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_5184_);
                            lean_dec(v___x_5118_);
                            v___x_5186_ = lean_box(0);
                            v_isShared_5187_ = v_isSharedCheck_5191_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            2 => {
                lean_inc(v___y_5134_);
                lean_inc_ref(v___y_5133_);
                lean_inc(v___y_5132_);
                lean_inc_ref(v___y_5131_);
                lean_inc(v___y_5130_);
                lean_inc_ref(v___y_5129_);
                lean_inc(v___y_5128_);
                lean_inc_ref(v___y_5127_);
                lean_inc(v___y_5126_);
                lean_inc(v___y_5125_);
                v___x_5135_ = lean_grind_cutsat_assert_eq(
                    v___x_5123_,
                    v___y_5125_,
                    v___y_5126_,
                    v___y_5127_,
                    v___y_5128_,
                    v___y_5129_,
                    v___y_5130_,
                    v___y_5131_,
                    v___y_5132_,
                    v___y_5133_,
                    v___y_5134_,
                );
                if lean_obj_tag(v___x_5135_) == 0 {
                    v_isSharedCheck_5150_ = (!lean_is_exclusive(v___x_5135_)) as u8;
                    if v_isSharedCheck_5150_ == 0 {
                        v_unused_5151_ = lean_ctor_get(v___x_5135_, 0);
                        lean_dec(v_unused_5151_);
                        v___x_5137_ = v___x_5135_;
                        v_isShared_5138_ = v_isSharedCheck_5150_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_5135_);
                        v___x_5137_ = lean_box(0);
                        v_isShared_5138_ = v_isSharedCheck_5150_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5108_);
                    lean_dec(v_snd_5106_);
                    v_a_5152_ = lean_ctor_get(v___x_5135_, 0);
                    v_isSharedCheck_5159_ = (!lean_is_exclusive(v___x_5135_)) as u8;
                    if v_isSharedCheck_5159_ == 0 {
                        v___x_5154_ = v___x_5135_;
                        v_isShared_5155_ = v_isSharedCheck_5159_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5152_);
                        lean_dec(v___x_5135_);
                        v___x_5154_ = lean_box(0);
                        v_isShared_5155_ = v_isSharedCheck_5159_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5139_ = lean_box((v___x_5113_) as usize);
                v___x_5140_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5140_, 0, v___x_5139_);
                if v_isShared_5109_ == 0 {
                    lean_ctor_set(v___x_5108_, 1, v___x_5112_);
                    lean_ctor_set(v___x_5108_, 0, v___x_5140_);
                    v___x_5142_ = v___x_5108_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5149_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5149_, 0, v___x_5140_);
                    lean_ctor_set(v_reuseFailAlloc_5149_, 1, v___x_5112_);
                    v___x_5142_ = v_reuseFailAlloc_5149_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5143_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5143_, 0, v___x_5142_);
                v___x_5144_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5144_, 0, v___x_5143_);
                v___x_5145_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5145_, 0, v___x_5144_);
                lean_ctor_set(v___x_5145_, 1, v_snd_5106_);
                if v_isShared_5138_ == 0 {
                    lean_ctor_set(v___x_5137_, 0, v___x_5145_);
                    v___x_5147_ = v___x_5137_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5148_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5148_, 0, v___x_5145_);
                    v___x_5147_ = v_reuseFailAlloc_5148_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5147_;
            }
            6 => {
                if v_isShared_5155_ == 0 {
                    v___x_5157_ = v___x_5154_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5158_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5158_, 0, v_a_5152_);
                    v___x_5157_ = v_reuseFailAlloc_5158_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5157_;
            }
            8 => {
                if v_isShared_5171_ == 0 {
                    v___x_5173_ = v___x_5170_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5174_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5174_, 0, v_a_5168_);
                    v___x_5173_ = v_reuseFailAlloc_5174_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5173_;
            }
            10 => {
                if v_isShared_5179_ == 0 {
                    v___x_5181_ = v___x_5178_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5182_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5182_, 0, v_a_5176_);
                    v___x_5181_ = v_reuseFailAlloc_5182_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5181_;
            }
            12 => {
                if v_isShared_5187_ == 0 {
                    v___x_5189_ = v___x_5186_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5190_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5190_, 0, v_a_5184_);
                    v___x_5189_ = v_reuseFailAlloc_5190_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5194_: *mut LeanObject = *_args.add(0);
    let mut v_c_5195_: *mut LeanObject = *_args.add(1);
    let mut v_as_5196_: *mut LeanObject = *_args.add(2);
    let mut v_sz_5197_: *mut LeanObject = *_args.add(3);
    let mut v_i_5198_: *mut LeanObject = *_args.add(4);
    let mut v_b_5199_: *mut LeanObject = *_args.add(5);
    let mut v___y_5200_: *mut LeanObject = *_args.add(6);
    let mut v___y_5201_: *mut LeanObject = *_args.add(7);
    let mut v___y_5202_: *mut LeanObject = *_args.add(8);
    let mut v___y_5203_: *mut LeanObject = *_args.add(9);
    let mut v___y_5204_: *mut LeanObject = *_args.add(10);
    let mut v___y_5205_: *mut LeanObject = *_args.add(11);
    let mut v___y_5206_: *mut LeanObject = *_args.add(12);
    let mut v___y_5207_: *mut LeanObject = *_args.add(13);
    let mut v___y_5208_: *mut LeanObject = *_args.add(14);
    let mut v___y_5209_: *mut LeanObject = *_args.add(15);
    let mut v___y_5210_: *mut LeanObject = *_args.add(16);
    let mut v_sz_boxed_5211_: usize = 0;
    let mut v_i_boxed_5212_: usize = 0;
    let mut v_res_5213_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5211_ = lean_unbox_usize(v_sz_5197_);
    lean_dec(v_sz_5197_);
    v_i_boxed_5212_ = lean_unbox_usize(v_i_5198_);
    lean_dec(v_i_5198_);
    v_res_5213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v___x_5194_, v_c_5195_, v_as_5196_, v_sz_boxed_5211_, v_i_boxed_5212_, v_b_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_);
    lean_dec(v___y_5209_);
    lean_dec_ref(v___y_5208_);
    lean_dec(v___y_5207_);
    lean_dec_ref(v___y_5206_);
    lean_dec(v___y_5205_);
    lean_dec_ref(v___y_5204_);
    lean_dec(v___y_5203_);
    lean_dec_ref(v___y_5202_);
    lean_dec(v___y_5201_);
    lean_dec(v___y_5200_);
    lean_dec_ref(v_as_5196_);
    return v_res_5213_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(
    mut v___x_5220_: *mut LeanObject,
    mut v_c_5221_: *mut LeanObject,
    mut v_as_5222_: *mut LeanObject,
    mut v_sz_5223_: usize,
    mut v_i_5224_: usize,
    mut v_b_5225_: *mut LeanObject,
    mut v___y_5226_: *mut LeanObject,
    mut v___y_5227_: *mut LeanObject,
    mut v___y_5228_: *mut LeanObject,
    mut v___y_5229_: *mut LeanObject,
    mut v___y_5230_: *mut LeanObject,
    mut v___y_5231_: *mut LeanObject,
    mut v___y_5232_: *mut LeanObject,
    mut v___y_5233_: *mut LeanObject,
    mut v___y_5234_: *mut LeanObject,
    mut v___y_5235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5237_: u8 = 0;
    let mut v___x_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5242_: u8 = 0;
    let mut v_a_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: u8 = 0;
    let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: usize = 0;
    let mut v___x_5249_: usize = 0;
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5254_: u8 = 0;
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5271_: u8 = 0;
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5283_: u8 = 0;
    let mut v_unused_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5288_: u8 = 0;
    let mut v___x_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5292_: u8 = 0;
    let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: u8 = 0;
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5304_: u8 = 0;
    let mut v___x_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5308_: u8 = 0;
    let mut v_a_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5312_: u8 = 0;
    let mut v___x_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5316_: u8 = 0;
    let mut v_a_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5320_: u8 = 0;
    let mut v___x_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5324_: u8 = 0;
    let mut v_isSharedCheck_5325_: u8 = 0;
    let mut v_unused_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5237_ = lean_usize_dec_lt(v_i_5224_, v_sz_5223_);
                if v___x_5237_ == 0 {
                    lean_dec_ref(v_c_5221_);
                    lean_dec_ref(v___x_5220_);
                    v___x_5238_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5238_, 0, v_b_5225_);
                    return v___x_5238_;
                } else {
                    v_snd_5239_ = lean_ctor_get(v_b_5225_, 1);
                    v_isSharedCheck_5325_ = (!lean_is_exclusive(v_b_5225_)) as u8;
                    if v_isSharedCheck_5325_ == 0 {
                        v_unused_5326_ = lean_ctor_get(v_b_5225_, 0);
                        lean_dec(v_unused_5326_);
                        v___x_5241_ = v_b_5225_;
                        v_isShared_5242_ = v_isSharedCheck_5325_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5239_);
                        lean_dec(v_b_5225_);
                        v___x_5241_ = lean_box(0);
                        v_isShared_5242_ = v_isSharedCheck_5325_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5243_ = lean_array_uget_borrowed(v_as_5222_, v_i_5224_);
                v_p_5244_ = lean_ctor_get(v_a_5243_, 0);
                v___x_5245_ = lean_box(0);
                v___x_5246_ = l_Int_Linear_Poly_isNegEq(v___x_5220_, v_p_5244_);
                if v___x_5246_ == 0 {
                    lean_del_object(v___x_5241_);
                    lean_dec(v_snd_5239_);
                    v___x_5247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1;
                    v___x_5248_ = 1usize;
                    v___x_5249_ = lean_usize_add(v_i_5224_, v___x_5248_);
                    v___x_5250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v___x_5220_, v_c_5221_, v_as_5222_, v_sz_5223_, v___x_5249_, v___x_5247_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
                    return v___x_5250_;
                } else {
                    lean_inc(v_a_5243_);
                    v___x_5251_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(
                        v_a_5243_,
                        v___y_5226_,
                        v___y_5232_,
                        v___y_5233_,
                        v___y_5234_,
                        v___y_5235_,
                    );
                    if lean_obj_tag(v___x_5251_) == 0 {
                        lean_dec_ref_known(v___x_5251_, 1);
                        v_options_5252_ = lean_ctor_get(v___y_5234_, 2);
                        v_inheritedTraceOptions_5253_ = lean_ctor_get(v___y_5234_, 13);
                        v_hasTrace_5254_ = lean_ctor_get_uint8(
                            v_options_5252_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        lean_inc(v_a_5243_);
                        v___x_5255_ = lean_alloc_ctor(8, 2, (0) as u32);
                        lean_ctor_set(v___x_5255_, 0, v_c_5221_);
                        lean_ctor_set(v___x_5255_, 1, v_a_5243_);
                        v___x_5256_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5256_, 0, v___x_5220_);
                        lean_ctor_set(v___x_5256_, 1, v___x_5255_);
                        if v_hasTrace_5254_ == 0 {
                            v___y_5258_ = v___y_5226_;
                            v___y_5259_ = v___y_5227_;
                            v___y_5260_ = v___y_5228_;
                            v___y_5261_ = v___y_5229_;
                            v___y_5262_ = v___y_5230_;
                            v___y_5263_ = v___y_5231_;
                            v___y_5264_ = v___y_5232_;
                            v___y_5265_ = v___y_5233_;
                            v___y_5266_ = v___y_5234_;
                            v___y_5267_ = v___y_5235_;
                            state = 2;
                            continue;
                        } else {
                            v___x_5293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4;
                            v___x_5294_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
                            v___x_5295_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_5253_,
                                v_options_5252_,
                                v___x_5294_,
                            );
                            if v___x_5295_ == 0 {
                                v___y_5258_ = v___y_5226_;
                                v___y_5259_ = v___y_5227_;
                                v___y_5260_ = v___y_5228_;
                                v___y_5261_ = v___y_5229_;
                                v___y_5262_ = v___y_5230_;
                                v___y_5263_ = v___y_5231_;
                                v___y_5264_ = v___y_5232_;
                                v___y_5265_ = v___y_5233_;
                                v___y_5266_ = v___y_5234_;
                                v___y_5267_ = v___y_5235_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc_ref(v___x_5256_);
                                v___x_5296_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(
                                    v___x_5256_,
                                    v___y_5226_,
                                    v___y_5234_,
                                );
                                if lean_obj_tag(v___x_5296_) == 0 {
                                    v_a_5297_ = lean_ctor_get(v___x_5296_, 0);
                                    lean_inc(v_a_5297_);
                                    lean_dec_ref_known(v___x_5296_, 1);
                                    v___x_5298_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
                                    v___x_5299_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_5299_, 0, v___x_5298_);
                                    lean_ctor_set(v___x_5299_, 1, v_a_5297_);
                                    v___x_5300_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_5293_, v___x_5299_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
                                    if lean_obj_tag(v___x_5300_) == 0 {
                                        lean_dec_ref_known(v___x_5300_, 1);
                                        v___y_5258_ = v___y_5226_;
                                        v___y_5259_ = v___y_5227_;
                                        v___y_5260_ = v___y_5228_;
                                        v___y_5261_ = v___y_5229_;
                                        v___y_5262_ = v___y_5230_;
                                        v___y_5263_ = v___y_5231_;
                                        v___y_5264_ = v___y_5232_;
                                        v___y_5265_ = v___y_5233_;
                                        v___y_5266_ = v___y_5234_;
                                        v___y_5267_ = v___y_5235_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec_ref_known(v___x_5256_, 2);
                                        lean_del_object(v___x_5241_);
                                        lean_dec(v_snd_5239_);
                                        v_a_5301_ = lean_ctor_get(v___x_5300_, 0);
                                        v_isSharedCheck_5308_ =
                                            (!lean_is_exclusive(v___x_5300_)) as u8;
                                        if v_isSharedCheck_5308_ == 0 {
                                            v___x_5303_ = v___x_5300_;
                                            v_isShared_5304_ = v_isSharedCheck_5308_;
                                            state = 8;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5301_);
                                            lean_dec(v___x_5300_);
                                            v___x_5303_ = lean_box(0);
                                            v_isShared_5304_ = v_isSharedCheck_5308_;
                                            state = 8;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref_known(v___x_5256_, 2);
                                    lean_del_object(v___x_5241_);
                                    lean_dec(v_snd_5239_);
                                    v_a_5309_ = lean_ctor_get(v___x_5296_, 0);
                                    v_isSharedCheck_5316_ = (!lean_is_exclusive(v___x_5296_)) as u8;
                                    if v_isSharedCheck_5316_ == 0 {
                                        v___x_5311_ = v___x_5296_;
                                        v_isShared_5312_ = v_isSharedCheck_5316_;
                                        state = 10;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5309_);
                                        lean_dec(v___x_5296_);
                                        v___x_5311_ = lean_box(0);
                                        v_isShared_5312_ = v_isSharedCheck_5316_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_5241_);
                        lean_dec(v_snd_5239_);
                        lean_dec_ref(v_c_5221_);
                        lean_dec_ref(v___x_5220_);
                        v_a_5317_ = lean_ctor_get(v___x_5251_, 0);
                        v_isSharedCheck_5324_ = (!lean_is_exclusive(v___x_5251_)) as u8;
                        if v_isSharedCheck_5324_ == 0 {
                            v___x_5319_ = v___x_5251_;
                            v_isShared_5320_ = v_isSharedCheck_5324_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_5317_);
                            lean_dec(v___x_5251_);
                            v___x_5319_ = lean_box(0);
                            v_isShared_5320_ = v_isSharedCheck_5324_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            2 => {
                lean_inc(v___y_5267_);
                lean_inc_ref(v___y_5266_);
                lean_inc(v___y_5265_);
                lean_inc_ref(v___y_5264_);
                lean_inc(v___y_5263_);
                lean_inc_ref(v___y_5262_);
                lean_inc(v___y_5261_);
                lean_inc_ref(v___y_5260_);
                lean_inc(v___y_5259_);
                lean_inc(v___y_5258_);
                v___x_5268_ = lean_grind_cutsat_assert_eq(
                    v___x_5256_,
                    v___y_5258_,
                    v___y_5259_,
                    v___y_5260_,
                    v___y_5261_,
                    v___y_5262_,
                    v___y_5263_,
                    v___y_5264_,
                    v___y_5265_,
                    v___y_5266_,
                    v___y_5267_,
                );
                if lean_obj_tag(v___x_5268_) == 0 {
                    v_isSharedCheck_5283_ = (!lean_is_exclusive(v___x_5268_)) as u8;
                    if v_isSharedCheck_5283_ == 0 {
                        v_unused_5284_ = lean_ctor_get(v___x_5268_, 0);
                        lean_dec(v_unused_5284_);
                        v___x_5270_ = v___x_5268_;
                        v_isShared_5271_ = v_isSharedCheck_5283_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_5268_);
                        v___x_5270_ = lean_box(0);
                        v_isShared_5271_ = v_isSharedCheck_5283_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5241_);
                    lean_dec(v_snd_5239_);
                    v_a_5285_ = lean_ctor_get(v___x_5268_, 0);
                    v_isSharedCheck_5292_ = (!lean_is_exclusive(v___x_5268_)) as u8;
                    if v_isSharedCheck_5292_ == 0 {
                        v___x_5287_ = v___x_5268_;
                        v_isShared_5288_ = v_isSharedCheck_5292_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5285_);
                        lean_dec(v___x_5268_);
                        v___x_5287_ = lean_box(0);
                        v_isShared_5288_ = v_isSharedCheck_5292_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5272_ = lean_box((v___x_5246_) as usize);
                v___x_5273_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5273_, 0, v___x_5272_);
                if v_isShared_5242_ == 0 {
                    lean_ctor_set(v___x_5241_, 1, v___x_5245_);
                    lean_ctor_set(v___x_5241_, 0, v___x_5273_);
                    v___x_5275_ = v___x_5241_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5282_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5282_, 0, v___x_5273_);
                    lean_ctor_set(v_reuseFailAlloc_5282_, 1, v___x_5245_);
                    v___x_5275_ = v_reuseFailAlloc_5282_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5276_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5276_, 0, v___x_5275_);
                v___x_5277_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5277_, 0, v___x_5276_);
                v___x_5278_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5278_, 0, v___x_5277_);
                lean_ctor_set(v___x_5278_, 1, v_snd_5239_);
                if v_isShared_5271_ == 0 {
                    lean_ctor_set(v___x_5270_, 0, v___x_5278_);
                    v___x_5280_ = v___x_5270_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5281_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5281_, 0, v___x_5278_);
                    v___x_5280_ = v_reuseFailAlloc_5281_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5280_;
            }
            6 => {
                if v_isShared_5288_ == 0 {
                    v___x_5290_ = v___x_5287_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5291_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5291_, 0, v_a_5285_);
                    v___x_5290_ = v_reuseFailAlloc_5291_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5290_;
            }
            8 => {
                if v_isShared_5304_ == 0 {
                    v___x_5306_ = v___x_5303_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5307_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5307_, 0, v_a_5301_);
                    v___x_5306_ = v_reuseFailAlloc_5307_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5306_;
            }
            10 => {
                if v_isShared_5312_ == 0 {
                    v___x_5314_ = v___x_5311_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5315_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5315_, 0, v_a_5309_);
                    v___x_5314_ = v_reuseFailAlloc_5315_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5314_;
            }
            12 => {
                if v_isShared_5320_ == 0 {
                    v___x_5322_ = v___x_5319_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5323_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5323_, 0, v_a_5317_);
                    v___x_5322_ = v_reuseFailAlloc_5323_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5322_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5327_: *mut LeanObject = *_args.add(0);
    let mut v_c_5328_: *mut LeanObject = *_args.add(1);
    let mut v_as_5329_: *mut LeanObject = *_args.add(2);
    let mut v_sz_5330_: *mut LeanObject = *_args.add(3);
    let mut v_i_5331_: *mut LeanObject = *_args.add(4);
    let mut v_b_5332_: *mut LeanObject = *_args.add(5);
    let mut v___y_5333_: *mut LeanObject = *_args.add(6);
    let mut v___y_5334_: *mut LeanObject = *_args.add(7);
    let mut v___y_5335_: *mut LeanObject = *_args.add(8);
    let mut v___y_5336_: *mut LeanObject = *_args.add(9);
    let mut v___y_5337_: *mut LeanObject = *_args.add(10);
    let mut v___y_5338_: *mut LeanObject = *_args.add(11);
    let mut v___y_5339_: *mut LeanObject = *_args.add(12);
    let mut v___y_5340_: *mut LeanObject = *_args.add(13);
    let mut v___y_5341_: *mut LeanObject = *_args.add(14);
    let mut v___y_5342_: *mut LeanObject = *_args.add(15);
    let mut v___y_5343_: *mut LeanObject = *_args.add(16);
    let mut v_sz_boxed_5344_: usize = 0;
    let mut v_i_boxed_5345_: usize = 0;
    let mut v_res_5346_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5344_ = lean_unbox_usize(v_sz_5330_);
    lean_dec(v_sz_5330_);
    v_i_boxed_5345_ = lean_unbox_usize(v_i_5331_);
    lean_dec(v_i_5331_);
    v_res_5346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v___x_5327_, v_c_5328_, v_as_5329_, v_sz_boxed_5344_, v_i_boxed_5345_, v_b_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_);
    lean_dec(v___y_5342_);
    lean_dec_ref(v___y_5341_);
    lean_dec(v___y_5340_);
    lean_dec_ref(v___y_5339_);
    lean_dec(v___y_5338_);
    lean_dec_ref(v___y_5337_);
    lean_dec(v___y_5336_);
    lean_dec_ref(v___y_5335_);
    lean_dec(v___y_5334_);
    lean_dec(v___y_5333_);
    lean_dec_ref(v_as_5329_);
    return v_res_5346_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(
    mut v_init_5347_: *mut LeanObject,
    mut v___x_5348_: *mut LeanObject,
    mut v_c_5349_: *mut LeanObject,
    mut v_n_5350_: *mut LeanObject,
    mut v_b_5351_: *mut LeanObject,
    mut v___y_5352_: *mut LeanObject,
    mut v___y_5353_: *mut LeanObject,
    mut v___y_5354_: *mut LeanObject,
    mut v___y_5355_: *mut LeanObject,
    mut v___y_5356_: *mut LeanObject,
    mut v___y_5357_: *mut LeanObject,
    mut v___y_5358_: *mut LeanObject,
    mut v___y_5359_: *mut LeanObject,
    mut v___y_5360_: *mut LeanObject,
    mut v___y_5361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5366_: usize = 0;
    let mut v___x_5367_: usize = 0;
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5372_: u8 = 0;
    let mut v_fst_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5383_: u8 = 0;
    let mut v_a_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5387_: u8 = 0;
    let mut v___x_5389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5391_: u8 = 0;
    let mut v_vs_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5395_: usize = 0;
    let mut v___x_5396_: usize = 0;
    let mut v___x_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5401_: u8 = 0;
    let mut v_fst_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5412_: u8 = 0;
    let mut v_a_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5416_: u8 = 0;
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5420_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_5350_) == 0 {
                    v_cs_5363_ = lean_ctor_get(v_n_5350_, 0);
                    v___x_5364_ = lean_box(0);
                    v___x_5365_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5365_, 0, v___x_5364_);
                    lean_ctor_set(v___x_5365_, 1, v_b_5351_);
                    v_sz_5366_ = lean_array_size(v_cs_5363_);
                    v___x_5367_ = 0usize;
                    v___x_5368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_5347_, v___x_5348_, v_c_5349_, v_cs_5363_, v_sz_5366_, v___x_5367_, v___x_5365_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_);
                    if lean_obj_tag(v___x_5368_) == 0 {
                        v_a_5369_ = lean_ctor_get(v___x_5368_, 0);
                        v_isSharedCheck_5383_ = (!lean_is_exclusive(v___x_5368_)) as u8;
                        if v_isSharedCheck_5383_ == 0 {
                            v___x_5371_ = v___x_5368_;
                            v_isShared_5372_ = v_isSharedCheck_5383_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5369_);
                            lean_dec(v___x_5368_);
                            v___x_5371_ = lean_box(0);
                            v_isShared_5372_ = v_isSharedCheck_5383_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5384_ = lean_ctor_get(v___x_5368_, 0);
                        v_isSharedCheck_5391_ = (!lean_is_exclusive(v___x_5368_)) as u8;
                        if v_isSharedCheck_5391_ == 0 {
                            v___x_5386_ = v___x_5368_;
                            v_isShared_5387_ = v_isSharedCheck_5391_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_5384_);
                            lean_dec(v___x_5368_);
                            v___x_5386_ = lean_box(0);
                            v_isShared_5387_ = v_isSharedCheck_5391_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_5392_ = lean_ctor_get(v_n_5350_, 0);
                    v___x_5393_ = lean_box(0);
                    v___x_5394_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5394_, 0, v___x_5393_);
                    lean_ctor_set(v___x_5394_, 1, v_b_5351_);
                    v_sz_5395_ = lean_array_size(v_vs_5392_);
                    v___x_5396_ = 0usize;
                    v___x_5397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v___x_5348_, v_c_5349_, v_vs_5392_, v_sz_5395_, v___x_5396_, v___x_5394_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_);
                    if lean_obj_tag(v___x_5397_) == 0 {
                        v_a_5398_ = lean_ctor_get(v___x_5397_, 0);
                        v_isSharedCheck_5412_ = (!lean_is_exclusive(v___x_5397_)) as u8;
                        if v_isSharedCheck_5412_ == 0 {
                            v___x_5400_ = v___x_5397_;
                            v_isShared_5401_ = v_isSharedCheck_5412_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5398_);
                            lean_dec(v___x_5397_);
                            v___x_5400_ = lean_box(0);
                            v_isShared_5401_ = v_isSharedCheck_5412_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5413_ = lean_ctor_get(v___x_5397_, 0);
                        v_isSharedCheck_5420_ = (!lean_is_exclusive(v___x_5397_)) as u8;
                        if v_isSharedCheck_5420_ == 0 {
                            v___x_5415_ = v___x_5397_;
                            v_isShared_5416_ = v_isSharedCheck_5420_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_5413_);
                            lean_dec(v___x_5397_);
                            v___x_5415_ = lean_box(0);
                            v_isShared_5416_ = v_isSharedCheck_5420_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5373_ = lean_ctor_get(v_a_5369_, 0);
                if lean_obj_tag(v_fst_5373_) == 0 {
                    v_snd_5374_ = lean_ctor_get(v_a_5369_, 1);
                    lean_inc(v_snd_5374_);
                    lean_dec(v_a_5369_);
                    v___x_5375_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5375_, 0, v_snd_5374_);
                    if v_isShared_5372_ == 0 {
                        lean_ctor_set(v___x_5371_, 0, v___x_5375_);
                        v___x_5377_ = v___x_5371_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5378_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5378_, 0, v___x_5375_);
                        v___x_5377_ = v_reuseFailAlloc_5378_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5373_);
                    lean_dec(v_a_5369_);
                    v_val_5379_ = lean_ctor_get(v_fst_5373_, 0);
                    lean_inc(v_val_5379_);
                    lean_dec_ref_known(v_fst_5373_, 1);
                    if v_isShared_5372_ == 0 {
                        lean_ctor_set(v___x_5371_, 0, v_val_5379_);
                        v___x_5381_ = v___x_5371_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5382_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5382_, 0, v_val_5379_);
                        v___x_5381_ = v_reuseFailAlloc_5382_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5377_;
            }
            3 => {
                return v___x_5381_;
            }
            4 => {
                if v_isShared_5387_ == 0 {
                    v___x_5389_ = v___x_5386_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5390_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5390_, 0, v_a_5384_);
                    v___x_5389_ = v_reuseFailAlloc_5390_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5389_;
            }
            6 => {
                v_fst_5402_ = lean_ctor_get(v_a_5398_, 0);
                if lean_obj_tag(v_fst_5402_) == 0 {
                    v_snd_5403_ = lean_ctor_get(v_a_5398_, 1);
                    lean_inc(v_snd_5403_);
                    lean_dec(v_a_5398_);
                    v___x_5404_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5404_, 0, v_snd_5403_);
                    if v_isShared_5401_ == 0 {
                        lean_ctor_set(v___x_5400_, 0, v___x_5404_);
                        v___x_5406_ = v___x_5400_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5407_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5407_, 0, v___x_5404_);
                        v___x_5406_ = v_reuseFailAlloc_5407_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5402_);
                    lean_dec(v_a_5398_);
                    v_val_5408_ = lean_ctor_get(v_fst_5402_, 0);
                    lean_inc(v_val_5408_);
                    lean_dec_ref_known(v_fst_5402_, 1);
                    if v_isShared_5401_ == 0 {
                        lean_ctor_set(v___x_5400_, 0, v_val_5408_);
                        v___x_5410_ = v___x_5400_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5411_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5411_, 0, v_val_5408_);
                        v___x_5410_ = v_reuseFailAlloc_5411_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_5406_;
            }
            8 => {
                return v___x_5410_;
            }
            9 => {
                if v_isShared_5416_ == 0 {
                    v___x_5418_ = v___x_5415_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5419_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5419_, 0, v_a_5413_);
                    v___x_5418_ = v_reuseFailAlloc_5419_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(
    mut v_init_5421_: *mut LeanObject,
    mut v___x_5422_: *mut LeanObject,
    mut v_c_5423_: *mut LeanObject,
    mut v_as_5424_: *mut LeanObject,
    mut v_sz_5425_: usize,
    mut v_i_5426_: usize,
    mut v_b_5427_: *mut LeanObject,
    mut v___y_5428_: *mut LeanObject,
    mut v___y_5429_: *mut LeanObject,
    mut v___y_5430_: *mut LeanObject,
    mut v___y_5431_: *mut LeanObject,
    mut v___y_5432_: *mut LeanObject,
    mut v___y_5433_: *mut LeanObject,
    mut v___y_5434_: *mut LeanObject,
    mut v___y_5435_: *mut LeanObject,
    mut v___y_5436_: *mut LeanObject,
    mut v___y_5437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5439_: u8 = 0;
    let mut v___x_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5444_: u8 = 0;
    let mut v_a_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5450_: u8 = 0;
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: usize = 0;
    let mut v___x_5463_: usize = 0;
    let mut v_reuseFailAlloc_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5466_: u8 = 0;
    let mut v_a_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5470_: u8 = 0;
    let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5474_: u8 = 0;
    let mut v_isSharedCheck_5475_: u8 = 0;
    let mut v_unused_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5439_ = lean_usize_dec_lt(v_i_5426_, v_sz_5425_);
                if v___x_5439_ == 0 {
                    lean_dec_ref(v_c_5423_);
                    lean_dec_ref(v___x_5422_);
                    v___x_5440_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5440_, 0, v_b_5427_);
                    return v___x_5440_;
                } else {
                    v_snd_5441_ = lean_ctor_get(v_b_5427_, 1);
                    v_isSharedCheck_5475_ = (!lean_is_exclusive(v_b_5427_)) as u8;
                    if v_isSharedCheck_5475_ == 0 {
                        v_unused_5476_ = lean_ctor_get(v_b_5427_, 0);
                        lean_dec(v_unused_5476_);
                        v___x_5443_ = v_b_5427_;
                        v_isShared_5444_ = v_isSharedCheck_5475_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5441_);
                        lean_dec(v_b_5427_);
                        v___x_5443_ = lean_box(0);
                        v_isShared_5444_ = v_isSharedCheck_5475_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5445_ = lean_array_uget_borrowed(v_as_5424_, v_i_5426_);
                lean_inc(v_snd_5441_);
                lean_inc_ref(v_c_5423_);
                lean_inc_ref(v___x_5422_);
                v___x_5446_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_5421_, v___x_5422_, v_c_5423_, v_a_5445_, v_snd_5441_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_);
                if lean_obj_tag(v___x_5446_) == 0 {
                    v_a_5447_ = lean_ctor_get(v___x_5446_, 0);
                    v_isSharedCheck_5466_ = (!lean_is_exclusive(v___x_5446_)) as u8;
                    if v_isSharedCheck_5466_ == 0 {
                        v___x_5449_ = v___x_5446_;
                        v_isShared_5450_ = v_isSharedCheck_5466_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5447_);
                        lean_dec(v___x_5446_);
                        v___x_5449_ = lean_box(0);
                        v_isShared_5450_ = v_isSharedCheck_5466_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5443_);
                    lean_dec(v_snd_5441_);
                    lean_dec_ref(v_c_5423_);
                    lean_dec_ref(v___x_5422_);
                    v_a_5467_ = lean_ctor_get(v___x_5446_, 0);
                    v_isSharedCheck_5474_ = (!lean_is_exclusive(v___x_5446_)) as u8;
                    if v_isSharedCheck_5474_ == 0 {
                        v___x_5469_ = v___x_5446_;
                        v_isShared_5470_ = v_isSharedCheck_5474_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5467_);
                        lean_dec(v___x_5446_);
                        v___x_5469_ = lean_box(0);
                        v_isShared_5470_ = v_isSharedCheck_5474_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_5447_) == 0 {
                    lean_dec_ref(v_c_5423_);
                    lean_dec_ref(v___x_5422_);
                    v___x_5451_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5451_, 0, v_a_5447_);
                    if v_isShared_5444_ == 0 {
                        lean_ctor_set(v___x_5443_, 0, v___x_5451_);
                        v___x_5453_ = v___x_5443_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5457_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5457_, 0, v___x_5451_);
                        lean_ctor_set(v_reuseFailAlloc_5457_, 1, v_snd_5441_);
                        v___x_5453_ = v_reuseFailAlloc_5457_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5449_);
                    lean_dec(v_snd_5441_);
                    v_a_5458_ = lean_ctor_get(v_a_5447_, 0);
                    lean_inc(v_a_5458_);
                    lean_dec_ref_known(v_a_5447_, 1);
                    v___x_5459_ = lean_box(0);
                    if v_isShared_5444_ == 0 {
                        lean_ctor_set(v___x_5443_, 1, v_a_5458_);
                        lean_ctor_set(v___x_5443_, 0, v___x_5459_);
                        v___x_5461_ = v___x_5443_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5465_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5465_, 0, v___x_5459_);
                        lean_ctor_set(v_reuseFailAlloc_5465_, 1, v_a_5458_);
                        v___x_5461_ = v_reuseFailAlloc_5465_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5450_ == 0 {
                    lean_ctor_set(v___x_5449_, 0, v___x_5453_);
                    v___x_5455_ = v___x_5449_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5456_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5456_, 0, v___x_5453_);
                    v___x_5455_ = v_reuseFailAlloc_5456_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5455_;
            }
            5 => {
                v___x_5462_ = 1usize;
                v___x_5463_ = lean_usize_add(v_i_5426_, v___x_5462_);
                v_i_5426_ = v___x_5463_;
                v_b_5427_ = v___x_5461_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_5470_ == 0 {
                    v___x_5472_ = v___x_5469_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5473_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5473_, 0, v_a_5467_);
                    v___x_5472_ = v_reuseFailAlloc_5473_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_init_5477_: *mut LeanObject = *_args.add(0);
    let mut v___x_5478_: *mut LeanObject = *_args.add(1);
    let mut v_c_5479_: *mut LeanObject = *_args.add(2);
    let mut v_as_5480_: *mut LeanObject = *_args.add(3);
    let mut v_sz_5481_: *mut LeanObject = *_args.add(4);
    let mut v_i_5482_: *mut LeanObject = *_args.add(5);
    let mut v_b_5483_: *mut LeanObject = *_args.add(6);
    let mut v___y_5484_: *mut LeanObject = *_args.add(7);
    let mut v___y_5485_: *mut LeanObject = *_args.add(8);
    let mut v___y_5486_: *mut LeanObject = *_args.add(9);
    let mut v___y_5487_: *mut LeanObject = *_args.add(10);
    let mut v___y_5488_: *mut LeanObject = *_args.add(11);
    let mut v___y_5489_: *mut LeanObject = *_args.add(12);
    let mut v___y_5490_: *mut LeanObject = *_args.add(13);
    let mut v___y_5491_: *mut LeanObject = *_args.add(14);
    let mut v___y_5492_: *mut LeanObject = *_args.add(15);
    let mut v___y_5493_: *mut LeanObject = *_args.add(16);
    let mut v___y_5494_: *mut LeanObject = *_args.add(17);
    let mut v_sz_boxed_5495_: usize = 0;
    let mut v_i_boxed_5496_: usize = 0;
    let mut v_res_5497_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5495_ = lean_unbox_usize(v_sz_5481_);
    lean_dec(v_sz_5481_);
    v_i_boxed_5496_ = lean_unbox_usize(v_i_5482_);
    lean_dec(v_i_5482_);
    v_res_5497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_5477_, v___x_5478_, v_c_5479_, v_as_5480_, v_sz_boxed_5495_, v_i_boxed_5496_, v_b_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_);
    lean_dec(v___y_5493_);
    lean_dec_ref(v___y_5492_);
    lean_dec(v___y_5491_);
    lean_dec_ref(v___y_5490_);
    lean_dec(v___y_5489_);
    lean_dec_ref(v___y_5488_);
    lean_dec(v___y_5487_);
    lean_dec_ref(v___y_5486_);
    lean_dec(v___y_5485_);
    lean_dec(v___y_5484_);
    lean_dec_ref(v_as_5480_);
    lean_dec_ref(v_init_5477_);
    return v_res_5497_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___boxed(
    mut v_init_5498_: *mut LeanObject,
    mut v___x_5499_: *mut LeanObject,
    mut v_c_5500_: *mut LeanObject,
    mut v_n_5501_: *mut LeanObject,
    mut v_b_5502_: *mut LeanObject,
    mut v___y_5503_: *mut LeanObject,
    mut v___y_5504_: *mut LeanObject,
    mut v___y_5505_: *mut LeanObject,
    mut v___y_5506_: *mut LeanObject,
    mut v___y_5507_: *mut LeanObject,
    mut v___y_5508_: *mut LeanObject,
    mut v___y_5509_: *mut LeanObject,
    mut v___y_5510_: *mut LeanObject,
    mut v___y_5511_: *mut LeanObject,
    mut v___y_5512_: *mut LeanObject,
    mut v___y_5513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5514_: *mut LeanObject = core::ptr::null_mut();
    v_res_5514_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_5498_, v___x_5499_, v_c_5500_, v_n_5501_, v_b_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_);
    lean_dec(v___y_5512_);
    lean_dec_ref(v___y_5511_);
    lean_dec(v___y_5510_);
    lean_dec_ref(v___y_5509_);
    lean_dec(v___y_5508_);
    lean_dec_ref(v___y_5507_);
    lean_dec(v___y_5506_);
    lean_dec_ref(v___y_5505_);
    lean_dec(v___y_5504_);
    lean_dec(v___y_5503_);
    lean_dec_ref(v_n_5501_);
    lean_dec_ref(v_init_5498_);
    return v_res_5514_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(
    mut v___x_5521_: *mut LeanObject,
    mut v_c_5522_: *mut LeanObject,
    mut v_as_5523_: *mut LeanObject,
    mut v_sz_5524_: usize,
    mut v_i_5525_: usize,
    mut v_b_5526_: *mut LeanObject,
    mut v___y_5527_: *mut LeanObject,
    mut v___y_5528_: *mut LeanObject,
    mut v___y_5529_: *mut LeanObject,
    mut v___y_5530_: *mut LeanObject,
    mut v___y_5531_: *mut LeanObject,
    mut v___y_5532_: *mut LeanObject,
    mut v___y_5533_: *mut LeanObject,
    mut v___y_5534_: *mut LeanObject,
    mut v___y_5535_: *mut LeanObject,
    mut v___y_5536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5538_: u8 = 0;
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5543_: u8 = 0;
    let mut v_a_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: u8 = 0;
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: usize = 0;
    let mut v___x_5550_: usize = 0;
    let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5555_: u8 = 0;
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5572_: u8 = 0;
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5583_: u8 = 0;
    let mut v_unused_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5588_: u8 = 0;
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5592_: u8 = 0;
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: u8 = 0;
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5604_: u8 = 0;
    let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5608_: u8 = 0;
    let mut v_a_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5612_: u8 = 0;
    let mut v___x_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5616_: u8 = 0;
    let mut v_a_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5620_: u8 = 0;
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5624_: u8 = 0;
    let mut v_isSharedCheck_5625_: u8 = 0;
    let mut v_unused_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5538_ = lean_usize_dec_lt(v_i_5525_, v_sz_5524_);
                if v___x_5538_ == 0 {
                    lean_dec_ref(v_c_5522_);
                    lean_dec_ref(v___x_5521_);
                    v___x_5539_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5539_, 0, v_b_5526_);
                    return v___x_5539_;
                } else {
                    v_snd_5540_ = lean_ctor_get(v_b_5526_, 1);
                    v_isSharedCheck_5625_ = (!lean_is_exclusive(v_b_5526_)) as u8;
                    if v_isSharedCheck_5625_ == 0 {
                        v_unused_5626_ = lean_ctor_get(v_b_5526_, 0);
                        lean_dec(v_unused_5626_);
                        v___x_5542_ = v_b_5526_;
                        v_isShared_5543_ = v_isSharedCheck_5625_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5540_);
                        lean_dec(v_b_5526_);
                        v___x_5542_ = lean_box(0);
                        v_isShared_5543_ = v_isSharedCheck_5625_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5544_ = lean_array_uget_borrowed(v_as_5523_, v_i_5525_);
                v_p_5545_ = lean_ctor_get(v_a_5544_, 0);
                v___x_5546_ = lean_box(0);
                v___x_5547_ = l_Int_Linear_Poly_isNegEq(v___x_5521_, v_p_5545_);
                if v___x_5547_ == 0 {
                    lean_del_object(v___x_5542_);
                    lean_dec(v_snd_5540_);
                    v___x_5548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1;
                    v___x_5549_ = 1usize;
                    v___x_5550_ = lean_usize_add(v_i_5525_, v___x_5549_);
                    v_i_5525_ = v___x_5550_;
                    v_b_5526_ = v___x_5548_;
                    state = 0;
                    continue;
                } else {
                    lean_inc(v_a_5544_);
                    v___x_5552_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(
                        v_a_5544_,
                        v___y_5527_,
                        v___y_5533_,
                        v___y_5534_,
                        v___y_5535_,
                        v___y_5536_,
                    );
                    if lean_obj_tag(v___x_5552_) == 0 {
                        lean_dec_ref_known(v___x_5552_, 1);
                        v_options_5553_ = lean_ctor_get(v___y_5535_, 2);
                        v_inheritedTraceOptions_5554_ = lean_ctor_get(v___y_5535_, 13);
                        v_hasTrace_5555_ = lean_ctor_get_uint8(
                            v_options_5553_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        lean_inc(v_a_5544_);
                        v___x_5556_ = lean_alloc_ctor(8, 2, (0) as u32);
                        lean_ctor_set(v___x_5556_, 0, v_c_5522_);
                        lean_ctor_set(v___x_5556_, 1, v_a_5544_);
                        v___x_5557_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5557_, 0, v___x_5521_);
                        lean_ctor_set(v___x_5557_, 1, v___x_5556_);
                        if v_hasTrace_5555_ == 0 {
                            v___y_5559_ = v___y_5527_;
                            v___y_5560_ = v___y_5528_;
                            v___y_5561_ = v___y_5529_;
                            v___y_5562_ = v___y_5530_;
                            v___y_5563_ = v___y_5531_;
                            v___y_5564_ = v___y_5532_;
                            v___y_5565_ = v___y_5533_;
                            v___y_5566_ = v___y_5534_;
                            v___y_5567_ = v___y_5535_;
                            v___y_5568_ = v___y_5536_;
                            state = 2;
                            continue;
                        } else {
                            v___x_5593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4;
                            v___x_5594_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
                            v___x_5595_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_5554_,
                                v_options_5553_,
                                v___x_5594_,
                            );
                            if v___x_5595_ == 0 {
                                v___y_5559_ = v___y_5527_;
                                v___y_5560_ = v___y_5528_;
                                v___y_5561_ = v___y_5529_;
                                v___y_5562_ = v___y_5530_;
                                v___y_5563_ = v___y_5531_;
                                v___y_5564_ = v___y_5532_;
                                v___y_5565_ = v___y_5533_;
                                v___y_5566_ = v___y_5534_;
                                v___y_5567_ = v___y_5535_;
                                v___y_5568_ = v___y_5536_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc_ref(v___x_5557_);
                                v___x_5596_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(
                                    v___x_5557_,
                                    v___y_5527_,
                                    v___y_5535_,
                                );
                                if lean_obj_tag(v___x_5596_) == 0 {
                                    v_a_5597_ = lean_ctor_get(v___x_5596_, 0);
                                    lean_inc(v_a_5597_);
                                    lean_dec_ref_known(v___x_5596_, 1);
                                    v___x_5598_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
                                    v___x_5599_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_5599_, 0, v___x_5598_);
                                    lean_ctor_set(v___x_5599_, 1, v_a_5597_);
                                    v___x_5600_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_5593_, v___x_5599_, v___y_5533_, v___y_5534_, v___y_5535_, v___y_5536_);
                                    if lean_obj_tag(v___x_5600_) == 0 {
                                        lean_dec_ref_known(v___x_5600_, 1);
                                        v___y_5559_ = v___y_5527_;
                                        v___y_5560_ = v___y_5528_;
                                        v___y_5561_ = v___y_5529_;
                                        v___y_5562_ = v___y_5530_;
                                        v___y_5563_ = v___y_5531_;
                                        v___y_5564_ = v___y_5532_;
                                        v___y_5565_ = v___y_5533_;
                                        v___y_5566_ = v___y_5534_;
                                        v___y_5567_ = v___y_5535_;
                                        v___y_5568_ = v___y_5536_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec_ref_known(v___x_5557_, 2);
                                        lean_del_object(v___x_5542_);
                                        lean_dec(v_snd_5540_);
                                        v_a_5601_ = lean_ctor_get(v___x_5600_, 0);
                                        v_isSharedCheck_5608_ =
                                            (!lean_is_exclusive(v___x_5600_)) as u8;
                                        if v_isSharedCheck_5608_ == 0 {
                                            v___x_5603_ = v___x_5600_;
                                            v_isShared_5604_ = v_isSharedCheck_5608_;
                                            state = 8;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5601_);
                                            lean_dec(v___x_5600_);
                                            v___x_5603_ = lean_box(0);
                                            v_isShared_5604_ = v_isSharedCheck_5608_;
                                            state = 8;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref_known(v___x_5557_, 2);
                                    lean_del_object(v___x_5542_);
                                    lean_dec(v_snd_5540_);
                                    v_a_5609_ = lean_ctor_get(v___x_5596_, 0);
                                    v_isSharedCheck_5616_ = (!lean_is_exclusive(v___x_5596_)) as u8;
                                    if v_isSharedCheck_5616_ == 0 {
                                        v___x_5611_ = v___x_5596_;
                                        v_isShared_5612_ = v_isSharedCheck_5616_;
                                        state = 10;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5609_);
                                        lean_dec(v___x_5596_);
                                        v___x_5611_ = lean_box(0);
                                        v_isShared_5612_ = v_isSharedCheck_5616_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_5542_);
                        lean_dec(v_snd_5540_);
                        lean_dec_ref(v_c_5522_);
                        lean_dec_ref(v___x_5521_);
                        v_a_5617_ = lean_ctor_get(v___x_5552_, 0);
                        v_isSharedCheck_5624_ = (!lean_is_exclusive(v___x_5552_)) as u8;
                        if v_isSharedCheck_5624_ == 0 {
                            v___x_5619_ = v___x_5552_;
                            v_isShared_5620_ = v_isSharedCheck_5624_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_5617_);
                            lean_dec(v___x_5552_);
                            v___x_5619_ = lean_box(0);
                            v_isShared_5620_ = v_isSharedCheck_5624_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            2 => {
                lean_inc(v___y_5568_);
                lean_inc_ref(v___y_5567_);
                lean_inc(v___y_5566_);
                lean_inc_ref(v___y_5565_);
                lean_inc(v___y_5564_);
                lean_inc_ref(v___y_5563_);
                lean_inc(v___y_5562_);
                lean_inc_ref(v___y_5561_);
                lean_inc(v___y_5560_);
                lean_inc(v___y_5559_);
                v___x_5569_ = lean_grind_cutsat_assert_eq(
                    v___x_5557_,
                    v___y_5559_,
                    v___y_5560_,
                    v___y_5561_,
                    v___y_5562_,
                    v___y_5563_,
                    v___y_5564_,
                    v___y_5565_,
                    v___y_5566_,
                    v___y_5567_,
                    v___y_5568_,
                );
                if lean_obj_tag(v___x_5569_) == 0 {
                    v_isSharedCheck_5583_ = (!lean_is_exclusive(v___x_5569_)) as u8;
                    if v_isSharedCheck_5583_ == 0 {
                        v_unused_5584_ = lean_ctor_get(v___x_5569_, 0);
                        lean_dec(v_unused_5584_);
                        v___x_5571_ = v___x_5569_;
                        v_isShared_5572_ = v_isSharedCheck_5583_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_5569_);
                        v___x_5571_ = lean_box(0);
                        v_isShared_5572_ = v_isSharedCheck_5583_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5542_);
                    lean_dec(v_snd_5540_);
                    v_a_5585_ = lean_ctor_get(v___x_5569_, 0);
                    v_isSharedCheck_5592_ = (!lean_is_exclusive(v___x_5569_)) as u8;
                    if v_isSharedCheck_5592_ == 0 {
                        v___x_5587_ = v___x_5569_;
                        v_isShared_5588_ = v_isSharedCheck_5592_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5585_);
                        lean_dec(v___x_5569_);
                        v___x_5587_ = lean_box(0);
                        v_isShared_5588_ = v_isSharedCheck_5592_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5573_ = lean_box((v___x_5547_) as usize);
                v___x_5574_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5574_, 0, v___x_5573_);
                if v_isShared_5543_ == 0 {
                    lean_ctor_set(v___x_5542_, 1, v___x_5546_);
                    lean_ctor_set(v___x_5542_, 0, v___x_5574_);
                    v___x_5576_ = v___x_5542_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5582_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5582_, 0, v___x_5574_);
                    lean_ctor_set(v_reuseFailAlloc_5582_, 1, v___x_5546_);
                    v___x_5576_ = v_reuseFailAlloc_5582_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5577_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5577_, 0, v___x_5576_);
                v___x_5578_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5578_, 0, v___x_5577_);
                lean_ctor_set(v___x_5578_, 1, v_snd_5540_);
                if v_isShared_5572_ == 0 {
                    lean_ctor_set(v___x_5571_, 0, v___x_5578_);
                    v___x_5580_ = v___x_5571_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5581_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5581_, 0, v___x_5578_);
                    v___x_5580_ = v_reuseFailAlloc_5581_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5580_;
            }
            6 => {
                if v_isShared_5588_ == 0 {
                    v___x_5590_ = v___x_5587_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5591_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_a_5585_);
                    v___x_5590_ = v_reuseFailAlloc_5591_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5590_;
            }
            8 => {
                if v_isShared_5604_ == 0 {
                    v___x_5606_ = v___x_5603_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5607_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5607_, 0, v_a_5601_);
                    v___x_5606_ = v_reuseFailAlloc_5607_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5606_;
            }
            10 => {
                if v_isShared_5612_ == 0 {
                    v___x_5614_ = v___x_5611_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5615_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5615_, 0, v_a_5609_);
                    v___x_5614_ = v_reuseFailAlloc_5615_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5614_;
            }
            12 => {
                if v_isShared_5620_ == 0 {
                    v___x_5622_ = v___x_5619_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5623_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5623_, 0, v_a_5617_);
                    v___x_5622_ = v_reuseFailAlloc_5623_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5622_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5627_: *mut LeanObject = *_args.add(0);
    let mut v_c_5628_: *mut LeanObject = *_args.add(1);
    let mut v_as_5629_: *mut LeanObject = *_args.add(2);
    let mut v_sz_5630_: *mut LeanObject = *_args.add(3);
    let mut v_i_5631_: *mut LeanObject = *_args.add(4);
    let mut v_b_5632_: *mut LeanObject = *_args.add(5);
    let mut v___y_5633_: *mut LeanObject = *_args.add(6);
    let mut v___y_5634_: *mut LeanObject = *_args.add(7);
    let mut v___y_5635_: *mut LeanObject = *_args.add(8);
    let mut v___y_5636_: *mut LeanObject = *_args.add(9);
    let mut v___y_5637_: *mut LeanObject = *_args.add(10);
    let mut v___y_5638_: *mut LeanObject = *_args.add(11);
    let mut v___y_5639_: *mut LeanObject = *_args.add(12);
    let mut v___y_5640_: *mut LeanObject = *_args.add(13);
    let mut v___y_5641_: *mut LeanObject = *_args.add(14);
    let mut v___y_5642_: *mut LeanObject = *_args.add(15);
    let mut v___y_5643_: *mut LeanObject = *_args.add(16);
    let mut v_sz_boxed_5644_: usize = 0;
    let mut v_i_boxed_5645_: usize = 0;
    let mut v_res_5646_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5644_ = lean_unbox_usize(v_sz_5630_);
    lean_dec(v_sz_5630_);
    v_i_boxed_5645_ = lean_unbox_usize(v_i_5631_);
    lean_dec(v_i_5631_);
    v_res_5646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v___x_5627_, v_c_5628_, v_as_5629_, v_sz_boxed_5644_, v_i_boxed_5645_, v_b_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_);
    lean_dec(v___y_5642_);
    lean_dec_ref(v___y_5641_);
    lean_dec(v___y_5640_);
    lean_dec_ref(v___y_5639_);
    lean_dec(v___y_5638_);
    lean_dec_ref(v___y_5637_);
    lean_dec(v___y_5636_);
    lean_dec_ref(v___y_5635_);
    lean_dec(v___y_5634_);
    lean_dec(v___y_5633_);
    lean_dec_ref(v_as_5629_);
    return v_res_5646_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(
    mut v___x_5650_: *mut LeanObject,
    mut v_c_5651_: *mut LeanObject,
    mut v_as_5652_: *mut LeanObject,
    mut v_sz_5653_: usize,
    mut v_i_5654_: usize,
    mut v_b_5655_: *mut LeanObject,
    mut v___y_5656_: *mut LeanObject,
    mut v___y_5657_: *mut LeanObject,
    mut v___y_5658_: *mut LeanObject,
    mut v___y_5659_: *mut LeanObject,
    mut v___y_5660_: *mut LeanObject,
    mut v___y_5661_: *mut LeanObject,
    mut v___y_5662_: *mut LeanObject,
    mut v___y_5663_: *mut LeanObject,
    mut v___y_5664_: *mut LeanObject,
    mut v___y_5665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5667_: u8 = 0;
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5672_: u8 = 0;
    let mut v_a_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: u8 = 0;
    let mut v___x_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: usize = 0;
    let mut v___x_5679_: usize = 0;
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5684_: u8 = 0;
    let mut v___x_5685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5701_: u8 = 0;
    let mut v___x_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5712_: u8 = 0;
    let mut v_unused_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5717_: u8 = 0;
    let mut v___x_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5721_: u8 = 0;
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: u8 = 0;
    let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5733_: u8 = 0;
    let mut v___x_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5737_: u8 = 0;
    let mut v_a_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5741_: u8 = 0;
    let mut v___x_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5745_: u8 = 0;
    let mut v_a_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5749_: u8 = 0;
    let mut v___x_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5753_: u8 = 0;
    let mut v_isSharedCheck_5754_: u8 = 0;
    let mut v_unused_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5667_ = lean_usize_dec_lt(v_i_5654_, v_sz_5653_);
                if v___x_5667_ == 0 {
                    lean_dec_ref(v_c_5651_);
                    lean_dec_ref(v___x_5650_);
                    v___x_5668_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5668_, 0, v_b_5655_);
                    return v___x_5668_;
                } else {
                    v_snd_5669_ = lean_ctor_get(v_b_5655_, 1);
                    v_isSharedCheck_5754_ = (!lean_is_exclusive(v_b_5655_)) as u8;
                    if v_isSharedCheck_5754_ == 0 {
                        v_unused_5755_ = lean_ctor_get(v_b_5655_, 0);
                        lean_dec(v_unused_5755_);
                        v___x_5671_ = v_b_5655_;
                        v_isShared_5672_ = v_isSharedCheck_5754_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5669_);
                        lean_dec(v_b_5655_);
                        v___x_5671_ = lean_box(0);
                        v_isShared_5672_ = v_isSharedCheck_5754_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5673_ = lean_array_uget_borrowed(v_as_5652_, v_i_5654_);
                v_p_5674_ = lean_ctor_get(v_a_5673_, 0);
                v___x_5675_ = lean_box(0);
                v___x_5676_ = l_Int_Linear_Poly_isNegEq(v___x_5650_, v_p_5674_);
                if v___x_5676_ == 0 {
                    lean_del_object(v___x_5671_);
                    lean_dec(v_snd_5669_);
                    v___x_5677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0;
                    v___x_5678_ = 1usize;
                    v___x_5679_ = lean_usize_add(v_i_5654_, v___x_5678_);
                    v___x_5680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v___x_5650_, v_c_5651_, v_as_5652_, v_sz_5653_, v___x_5679_, v___x_5677_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_, v___y_5665_);
                    return v___x_5680_;
                } else {
                    lean_inc(v_a_5673_);
                    v___x_5681_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(
                        v_a_5673_,
                        v___y_5656_,
                        v___y_5662_,
                        v___y_5663_,
                        v___y_5664_,
                        v___y_5665_,
                    );
                    if lean_obj_tag(v___x_5681_) == 0 {
                        lean_dec_ref_known(v___x_5681_, 1);
                        v_options_5682_ = lean_ctor_get(v___y_5664_, 2);
                        v_inheritedTraceOptions_5683_ = lean_ctor_get(v___y_5664_, 13);
                        v_hasTrace_5684_ = lean_ctor_get_uint8(
                            v_options_5682_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        lean_inc(v_a_5673_);
                        v___x_5685_ = lean_alloc_ctor(8, 2, (0) as u32);
                        lean_ctor_set(v___x_5685_, 0, v_c_5651_);
                        lean_ctor_set(v___x_5685_, 1, v_a_5673_);
                        v___x_5686_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5686_, 0, v___x_5650_);
                        lean_ctor_set(v___x_5686_, 1, v___x_5685_);
                        if v_hasTrace_5684_ == 0 {
                            v___y_5688_ = v___y_5656_;
                            v___y_5689_ = v___y_5657_;
                            v___y_5690_ = v___y_5658_;
                            v___y_5691_ = v___y_5659_;
                            v___y_5692_ = v___y_5660_;
                            v___y_5693_ = v___y_5661_;
                            v___y_5694_ = v___y_5662_;
                            v___y_5695_ = v___y_5663_;
                            v___y_5696_ = v___y_5664_;
                            v___y_5697_ = v___y_5665_;
                            state = 2;
                            continue;
                        } else {
                            v___x_5722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4;
                            v___x_5723_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
                            v___x_5724_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_5683_,
                                v_options_5682_,
                                v___x_5723_,
                            );
                            if v___x_5724_ == 0 {
                                v___y_5688_ = v___y_5656_;
                                v___y_5689_ = v___y_5657_;
                                v___y_5690_ = v___y_5658_;
                                v___y_5691_ = v___y_5659_;
                                v___y_5692_ = v___y_5660_;
                                v___y_5693_ = v___y_5661_;
                                v___y_5694_ = v___y_5662_;
                                v___y_5695_ = v___y_5663_;
                                v___y_5696_ = v___y_5664_;
                                v___y_5697_ = v___y_5665_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc_ref(v___x_5686_);
                                v___x_5725_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(
                                    v___x_5686_,
                                    v___y_5656_,
                                    v___y_5664_,
                                );
                                if lean_obj_tag(v___x_5725_) == 0 {
                                    v_a_5726_ = lean_ctor_get(v___x_5725_, 0);
                                    lean_inc(v_a_5726_);
                                    lean_dec_ref_known(v___x_5725_, 1);
                                    v___x_5727_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
                                    v___x_5728_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_5728_, 0, v___x_5727_);
                                    lean_ctor_set(v___x_5728_, 1, v_a_5726_);
                                    v___x_5729_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_5722_, v___x_5728_, v___y_5662_, v___y_5663_, v___y_5664_, v___y_5665_);
                                    if lean_obj_tag(v___x_5729_) == 0 {
                                        lean_dec_ref_known(v___x_5729_, 1);
                                        v___y_5688_ = v___y_5656_;
                                        v___y_5689_ = v___y_5657_;
                                        v___y_5690_ = v___y_5658_;
                                        v___y_5691_ = v___y_5659_;
                                        v___y_5692_ = v___y_5660_;
                                        v___y_5693_ = v___y_5661_;
                                        v___y_5694_ = v___y_5662_;
                                        v___y_5695_ = v___y_5663_;
                                        v___y_5696_ = v___y_5664_;
                                        v___y_5697_ = v___y_5665_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec_ref_known(v___x_5686_, 2);
                                        lean_del_object(v___x_5671_);
                                        lean_dec(v_snd_5669_);
                                        v_a_5730_ = lean_ctor_get(v___x_5729_, 0);
                                        v_isSharedCheck_5737_ =
                                            (!lean_is_exclusive(v___x_5729_)) as u8;
                                        if v_isSharedCheck_5737_ == 0 {
                                            v___x_5732_ = v___x_5729_;
                                            v_isShared_5733_ = v_isSharedCheck_5737_;
                                            state = 8;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5730_);
                                            lean_dec(v___x_5729_);
                                            v___x_5732_ = lean_box(0);
                                            v_isShared_5733_ = v_isSharedCheck_5737_;
                                            state = 8;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref_known(v___x_5686_, 2);
                                    lean_del_object(v___x_5671_);
                                    lean_dec(v_snd_5669_);
                                    v_a_5738_ = lean_ctor_get(v___x_5725_, 0);
                                    v_isSharedCheck_5745_ = (!lean_is_exclusive(v___x_5725_)) as u8;
                                    if v_isSharedCheck_5745_ == 0 {
                                        v___x_5740_ = v___x_5725_;
                                        v_isShared_5741_ = v_isSharedCheck_5745_;
                                        state = 10;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5738_);
                                        lean_dec(v___x_5725_);
                                        v___x_5740_ = lean_box(0);
                                        v_isShared_5741_ = v_isSharedCheck_5745_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_5671_);
                        lean_dec(v_snd_5669_);
                        lean_dec_ref(v_c_5651_);
                        lean_dec_ref(v___x_5650_);
                        v_a_5746_ = lean_ctor_get(v___x_5681_, 0);
                        v_isSharedCheck_5753_ = (!lean_is_exclusive(v___x_5681_)) as u8;
                        if v_isSharedCheck_5753_ == 0 {
                            v___x_5748_ = v___x_5681_;
                            v_isShared_5749_ = v_isSharedCheck_5753_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_5746_);
                            lean_dec(v___x_5681_);
                            v___x_5748_ = lean_box(0);
                            v_isShared_5749_ = v_isSharedCheck_5753_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            2 => {
                lean_inc(v___y_5697_);
                lean_inc_ref(v___y_5696_);
                lean_inc(v___y_5695_);
                lean_inc_ref(v___y_5694_);
                lean_inc(v___y_5693_);
                lean_inc_ref(v___y_5692_);
                lean_inc(v___y_5691_);
                lean_inc_ref(v___y_5690_);
                lean_inc(v___y_5689_);
                lean_inc(v___y_5688_);
                v___x_5698_ = lean_grind_cutsat_assert_eq(
                    v___x_5686_,
                    v___y_5688_,
                    v___y_5689_,
                    v___y_5690_,
                    v___y_5691_,
                    v___y_5692_,
                    v___y_5693_,
                    v___y_5694_,
                    v___y_5695_,
                    v___y_5696_,
                    v___y_5697_,
                );
                if lean_obj_tag(v___x_5698_) == 0 {
                    v_isSharedCheck_5712_ = (!lean_is_exclusive(v___x_5698_)) as u8;
                    if v_isSharedCheck_5712_ == 0 {
                        v_unused_5713_ = lean_ctor_get(v___x_5698_, 0);
                        lean_dec(v_unused_5713_);
                        v___x_5700_ = v___x_5698_;
                        v_isShared_5701_ = v_isSharedCheck_5712_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_5698_);
                        v___x_5700_ = lean_box(0);
                        v_isShared_5701_ = v_isSharedCheck_5712_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5671_);
                    lean_dec(v_snd_5669_);
                    v_a_5714_ = lean_ctor_get(v___x_5698_, 0);
                    v_isSharedCheck_5721_ = (!lean_is_exclusive(v___x_5698_)) as u8;
                    if v_isSharedCheck_5721_ == 0 {
                        v___x_5716_ = v___x_5698_;
                        v_isShared_5717_ = v_isSharedCheck_5721_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5714_);
                        lean_dec(v___x_5698_);
                        v___x_5716_ = lean_box(0);
                        v_isShared_5717_ = v_isSharedCheck_5721_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5702_ = lean_box((v___x_5676_) as usize);
                v___x_5703_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5703_, 0, v___x_5702_);
                if v_isShared_5672_ == 0 {
                    lean_ctor_set(v___x_5671_, 1, v___x_5675_);
                    lean_ctor_set(v___x_5671_, 0, v___x_5703_);
                    v___x_5705_ = v___x_5671_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5711_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5711_, 0, v___x_5703_);
                    lean_ctor_set(v_reuseFailAlloc_5711_, 1, v___x_5675_);
                    v___x_5705_ = v_reuseFailAlloc_5711_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5706_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5706_, 0, v___x_5705_);
                v___x_5707_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5707_, 0, v___x_5706_);
                lean_ctor_set(v___x_5707_, 1, v_snd_5669_);
                if v_isShared_5701_ == 0 {
                    lean_ctor_set(v___x_5700_, 0, v___x_5707_);
                    v___x_5709_ = v___x_5700_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5710_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5710_, 0, v___x_5707_);
                    v___x_5709_ = v_reuseFailAlloc_5710_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5709_;
            }
            6 => {
                if v_isShared_5717_ == 0 {
                    v___x_5719_ = v___x_5716_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5720_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5720_, 0, v_a_5714_);
                    v___x_5719_ = v_reuseFailAlloc_5720_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5719_;
            }
            8 => {
                if v_isShared_5733_ == 0 {
                    v___x_5735_ = v___x_5732_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5736_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5736_, 0, v_a_5730_);
                    v___x_5735_ = v_reuseFailAlloc_5736_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5735_;
            }
            10 => {
                if v_isShared_5741_ == 0 {
                    v___x_5743_ = v___x_5740_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5744_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5744_, 0, v_a_5738_);
                    v___x_5743_ = v_reuseFailAlloc_5744_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5743_;
            }
            12 => {
                if v_isShared_5749_ == 0 {
                    v___x_5751_ = v___x_5748_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5752_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5752_, 0, v_a_5746_);
                    v___x_5751_ = v_reuseFailAlloc_5752_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5751_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5756_: *mut LeanObject = *_args.add(0);
    let mut v_c_5757_: *mut LeanObject = *_args.add(1);
    let mut v_as_5758_: *mut LeanObject = *_args.add(2);
    let mut v_sz_5759_: *mut LeanObject = *_args.add(3);
    let mut v_i_5760_: *mut LeanObject = *_args.add(4);
    let mut v_b_5761_: *mut LeanObject = *_args.add(5);
    let mut v___y_5762_: *mut LeanObject = *_args.add(6);
    let mut v___y_5763_: *mut LeanObject = *_args.add(7);
    let mut v___y_5764_: *mut LeanObject = *_args.add(8);
    let mut v___y_5765_: *mut LeanObject = *_args.add(9);
    let mut v___y_5766_: *mut LeanObject = *_args.add(10);
    let mut v___y_5767_: *mut LeanObject = *_args.add(11);
    let mut v___y_5768_: *mut LeanObject = *_args.add(12);
    let mut v___y_5769_: *mut LeanObject = *_args.add(13);
    let mut v___y_5770_: *mut LeanObject = *_args.add(14);
    let mut v___y_5771_: *mut LeanObject = *_args.add(15);
    let mut v___y_5772_: *mut LeanObject = *_args.add(16);
    let mut v_sz_boxed_5773_: usize = 0;
    let mut v_i_boxed_5774_: usize = 0;
    let mut v_res_5775_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5773_ = lean_unbox_usize(v_sz_5759_);
    lean_dec(v_sz_5759_);
    v_i_boxed_5774_ = lean_unbox_usize(v_i_5760_);
    lean_dec(v_i_5760_);
    v_res_5775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v___x_5756_, v_c_5757_, v_as_5758_, v_sz_boxed_5773_, v_i_boxed_5774_, v_b_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_, v___y_5770_, v___y_5771_);
    lean_dec(v___y_5771_);
    lean_dec_ref(v___y_5770_);
    lean_dec(v___y_5769_);
    lean_dec_ref(v___y_5768_);
    lean_dec(v___y_5767_);
    lean_dec_ref(v___y_5766_);
    lean_dec(v___y_5765_);
    lean_dec_ref(v___y_5764_);
    lean_dec(v___y_5763_);
    lean_dec(v___y_5762_);
    lean_dec_ref(v_as_5758_);
    return v_res_5775_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(
    mut v___x_5776_: *mut LeanObject,
    mut v_c_5777_: *mut LeanObject,
    mut v_t_5778_: *mut LeanObject,
    mut v_init_5779_: *mut LeanObject,
    mut v___y_5780_: *mut LeanObject,
    mut v___y_5781_: *mut LeanObject,
    mut v___y_5782_: *mut LeanObject,
    mut v___y_5783_: *mut LeanObject,
    mut v___y_5784_: *mut LeanObject,
    mut v___y_5785_: *mut LeanObject,
    mut v___y_5786_: *mut LeanObject,
    mut v___y_5787_: *mut LeanObject,
    mut v___y_5788_: *mut LeanObject,
    mut v___y_5789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5797_: u8 = 0;
    let mut v_a_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5805_: usize = 0;
    let mut v___x_5806_: usize = 0;
    let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5811_: u8 = 0;
    let mut v_fst_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5821_: u8 = 0;
    let mut v_a_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5825_: u8 = 0;
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5829_: u8 = 0;
    let mut v_isSharedCheck_5830_: u8 = 0;
    let mut v_a_5831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5834_: u8 = 0;
    let mut v___x_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5838_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5791_ = lean_ctor_get(v_t_5778_, 0);
                v_tail_5792_ = lean_ctor_get(v_t_5778_, 1);
                lean_inc_ref(v_c_5777_);
                lean_inc_ref(v___x_5776_);
                lean_inc_ref(v_init_5779_);
                v___x_5793_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_5779_, v___x_5776_, v_c_5777_, v_root_5791_, v_init_5779_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_);
                lean_dec_ref(v_init_5779_);
                if lean_obj_tag(v___x_5793_) == 0 {
                    v_a_5794_ = lean_ctor_get(v___x_5793_, 0);
                    v_isSharedCheck_5830_ = (!lean_is_exclusive(v___x_5793_)) as u8;
                    if v_isSharedCheck_5830_ == 0 {
                        v___x_5796_ = v___x_5793_;
                        v_isShared_5797_ = v_isSharedCheck_5830_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5794_);
                        lean_dec(v___x_5793_);
                        v___x_5796_ = lean_box(0);
                        v_isShared_5797_ = v_isSharedCheck_5830_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_c_5777_);
                    lean_dec_ref(v___x_5776_);
                    v_a_5831_ = lean_ctor_get(v___x_5793_, 0);
                    v_isSharedCheck_5838_ = (!lean_is_exclusive(v___x_5793_)) as u8;
                    if v_isSharedCheck_5838_ == 0 {
                        v___x_5833_ = v___x_5793_;
                        v_isShared_5834_ = v_isSharedCheck_5838_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5831_);
                        lean_dec(v___x_5793_);
                        v___x_5833_ = lean_box(0);
                        v_isShared_5834_ = v_isSharedCheck_5838_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_5794_) == 0 {
                    lean_dec_ref(v_c_5777_);
                    lean_dec_ref(v___x_5776_);
                    v_a_5798_ = lean_ctor_get(v_a_5794_, 0);
                    lean_inc(v_a_5798_);
                    lean_dec_ref_known(v_a_5794_, 1);
                    if v_isShared_5797_ == 0 {
                        lean_ctor_set(v___x_5796_, 0, v_a_5798_);
                        v___x_5800_ = v___x_5796_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5801_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5801_, 0, v_a_5798_);
                        v___x_5800_ = v_reuseFailAlloc_5801_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5796_);
                    v_a_5802_ = lean_ctor_get(v_a_5794_, 0);
                    lean_inc(v_a_5802_);
                    lean_dec_ref_known(v_a_5794_, 1);
                    v___x_5803_ = lean_box(0);
                    v___x_5804_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5804_, 0, v___x_5803_);
                    lean_ctor_set(v___x_5804_, 1, v_a_5802_);
                    v_sz_5805_ = lean_array_size(v_tail_5792_);
                    v___x_5806_ = 0usize;
                    v___x_5807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v___x_5776_, v_c_5777_, v_tail_5792_, v_sz_5805_, v___x_5806_, v___x_5804_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_);
                    if lean_obj_tag(v___x_5807_) == 0 {
                        v_a_5808_ = lean_ctor_get(v___x_5807_, 0);
                        v_isSharedCheck_5821_ = (!lean_is_exclusive(v___x_5807_)) as u8;
                        if v_isSharedCheck_5821_ == 0 {
                            v___x_5810_ = v___x_5807_;
                            v_isShared_5811_ = v_isSharedCheck_5821_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5808_);
                            lean_dec(v___x_5807_);
                            v___x_5810_ = lean_box(0);
                            v_isShared_5811_ = v_isSharedCheck_5821_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5822_ = lean_ctor_get(v___x_5807_, 0);
                        v_isSharedCheck_5829_ = (!lean_is_exclusive(v___x_5807_)) as u8;
                        if v_isSharedCheck_5829_ == 0 {
                            v___x_5824_ = v___x_5807_;
                            v_isShared_5825_ = v_isSharedCheck_5829_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5822_);
                            lean_dec(v___x_5807_);
                            v___x_5824_ = lean_box(0);
                            v_isShared_5825_ = v_isSharedCheck_5829_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5800_;
            }
            3 => {
                v_fst_5812_ = lean_ctor_get(v_a_5808_, 0);
                if lean_obj_tag(v_fst_5812_) == 0 {
                    v_snd_5813_ = lean_ctor_get(v_a_5808_, 1);
                    lean_inc(v_snd_5813_);
                    lean_dec(v_a_5808_);
                    if v_isShared_5811_ == 0 {
                        lean_ctor_set(v___x_5810_, 0, v_snd_5813_);
                        v___x_5815_ = v___x_5810_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5816_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5816_, 0, v_snd_5813_);
                        v___x_5815_ = v_reuseFailAlloc_5816_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5812_);
                    lean_dec(v_a_5808_);
                    v_val_5817_ = lean_ctor_get(v_fst_5812_, 0);
                    lean_inc(v_val_5817_);
                    lean_dec_ref_known(v_fst_5812_, 1);
                    if v_isShared_5811_ == 0 {
                        lean_ctor_set(v___x_5810_, 0, v_val_5817_);
                        v___x_5819_ = v___x_5810_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5820_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5820_, 0, v_val_5817_);
                        v___x_5819_ = v_reuseFailAlloc_5820_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5815_;
            }
            5 => {
                return v___x_5819_;
            }
            6 => {
                if v_isShared_5825_ == 0 {
                    v___x_5827_ = v___x_5824_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5828_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5828_, 0, v_a_5822_);
                    v___x_5827_ = v_reuseFailAlloc_5828_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5827_;
            }
            8 => {
                if v_isShared_5834_ == 0 {
                    v___x_5836_ = v___x_5833_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5837_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5837_, 0, v_a_5831_);
                    v___x_5836_ = v_reuseFailAlloc_5837_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5836_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___boxed(
    mut v___x_5839_: *mut LeanObject,
    mut v_c_5840_: *mut LeanObject,
    mut v_t_5841_: *mut LeanObject,
    mut v_init_5842_: *mut LeanObject,
    mut v___y_5843_: *mut LeanObject,
    mut v___y_5844_: *mut LeanObject,
    mut v___y_5845_: *mut LeanObject,
    mut v___y_5846_: *mut LeanObject,
    mut v___y_5847_: *mut LeanObject,
    mut v___y_5848_: *mut LeanObject,
    mut v___y_5849_: *mut LeanObject,
    mut v___y_5850_: *mut LeanObject,
    mut v___y_5851_: *mut LeanObject,
    mut v___y_5852_: *mut LeanObject,
    mut v___y_5853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5854_: *mut LeanObject = core::ptr::null_mut();
    v_res_5854_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v___x_5839_, v_c_5840_, v_t_5841_, v_init_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_, v___y_5847_, v___y_5848_, v___y_5849_, v___y_5850_, v___y_5851_, v___y_5852_);
    lean_dec(v___y_5852_);
    lean_dec_ref(v___y_5851_);
    lean_dec(v___y_5850_);
    lean_dec_ref(v___y_5849_);
    lean_dec(v___y_5848_);
    lean_dec_ref(v___y_5847_);
    lean_dec(v___y_5846_);
    lean_dec_ref(v___y_5845_);
    lean_dec(v___y_5844_);
    lean_dec(v___y_5843_);
    lean_dec_ref(v_t_5841_);
    return v_res_5854_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0()
-> *mut LeanObject {
    let mut v___x_5855_: *mut LeanObject = core::ptr::null_mut();
    v___x_5855_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
    return v___x_5855_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(
    mut v_c_5856_: *mut LeanObject,
    mut v_a_5857_: *mut LeanObject,
    mut v_a_5858_: *mut LeanObject,
    mut v_a_5859_: *mut LeanObject,
    mut v_a_5860_: *mut LeanObject,
    mut v_a_5861_: *mut LeanObject,
    mut v_a_5862_: *mut LeanObject,
    mut v_a_5863_: *mut LeanObject,
    mut v_a_5864_: *mut LeanObject,
    mut v_a_5865_: *mut LeanObject,
    mut v_a_5866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5880_: u8 = 0;
    let mut v_fst_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: u8 = 0;
    let mut v___x_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5891_: u8 = 0;
    let mut v_a_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5895_: u8 = 0;
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5899_: u8 = 0;
    let mut v___x_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: u8 = 0;
    let mut v_lowers_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: u8 = 0;
    let mut v___x_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uppers_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: u8 = 0;
    let mut v___x_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5917_: u8 = 0;
    let mut v___x_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5921_: u8 = 0;
    let mut v___x_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_5868_ = lean_ctor_get(v_c_5856_, 0);
                if lean_obj_tag(v_p_5868_) == 1 {
                    lean_inc_ref(v_p_5868_);
                    v_k_5869_ = lean_ctor_get(v_p_5868_, 0);
                    v_v_5870_ = lean_ctor_get(v_p_5868_, 1);
                    v___x_5871_ =
                        l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_5857_, v_a_5865_);
                    if lean_obj_tag(v___x_5871_) == 0 {
                        v_a_5872_ = lean_ctor_get(v___x_5871_, 0);
                        lean_inc(v_a_5872_);
                        lean_dec_ref_known(v___x_5871_, 1);
                        v___x_5900_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9,
                        );
                        v___x_5901_ = lean_int_dec_lt(v_k_5869_, v___x_5900_);
                        if v___x_5901_ == 0 {
                            v_lowers_5902_ = lean_ctor_get(v_a_5872_, 7);
                            lean_inc_ref(v_lowers_5902_);
                            lean_dec(v_a_5872_);
                            v_size_5903_ = lean_ctor_get(v_lowers_5902_, 2);
                            v___x_5904_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
                            v___x_5905_ = lean_nat_dec_lt(v_v_5870_, v_size_5903_);
                            if v___x_5905_ == 0 {
                                lean_dec_ref(v_lowers_5902_);
                                v___x_5906_ = l_outOfBounds___redArg(v___x_5904_);
                                v___y_5874_ = v___x_5906_;
                                state = 1;
                                continue;
                            } else {
                                v___x_5907_ = l_Lean_PersistentArray_get_x21___redArg(
                                    v___x_5904_,
                                    v_lowers_5902_,
                                    v_v_5870_,
                                );
                                lean_dec_ref(v_lowers_5902_);
                                v___y_5874_ = v___x_5907_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_uppers_5908_ = lean_ctor_get(v_a_5872_, 8);
                            lean_inc_ref(v_uppers_5908_);
                            lean_dec(v_a_5872_);
                            v_size_5909_ = lean_ctor_get(v_uppers_5908_, 2);
                            v___x_5910_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
                            v___x_5911_ = lean_nat_dec_lt(v_v_5870_, v_size_5909_);
                            if v___x_5911_ == 0 {
                                lean_dec_ref(v_uppers_5908_);
                                v___x_5912_ = l_outOfBounds___redArg(v___x_5910_);
                                v___y_5874_ = v___x_5912_;
                                state = 1;
                                continue;
                            } else {
                                v___x_5913_ = l_Lean_PersistentArray_get_x21___redArg(
                                    v___x_5910_,
                                    v_uppers_5908_,
                                    v_v_5870_,
                                );
                                lean_dec_ref(v_uppers_5908_);
                                v___y_5874_ = v___x_5913_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_p_5868_, 3);
                        lean_dec_ref(v_c_5856_);
                        v_a_5914_ = lean_ctor_get(v___x_5871_, 0);
                        v_isSharedCheck_5921_ = (!lean_is_exclusive(v___x_5871_)) as u8;
                        if v_isSharedCheck_5921_ == 0 {
                            v___x_5916_ = v___x_5871_;
                            v_isShared_5917_ = v_isSharedCheck_5921_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5914_);
                            lean_dec(v___x_5871_);
                            v___x_5916_ = lean_box(0);
                            v_isShared_5917_ = v_isSharedCheck_5921_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v___x_5922_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(
                        v_c_5856_, v_a_5857_, v_a_5863_, v_a_5864_, v_a_5865_, v_a_5866_,
                    );
                    return v___x_5922_;
                }
            }
            1 => {
                v___x_5875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0;
                v___x_5876_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_p_5868_, v_c_5856_, v___y_5874_, v___x_5875_, v_a_5857_, v_a_5858_, v_a_5859_, v_a_5860_, v_a_5861_, v_a_5862_, v_a_5863_, v_a_5864_, v_a_5865_, v_a_5866_);
                lean_dec_ref(v___y_5874_);
                if lean_obj_tag(v___x_5876_) == 0 {
                    v_a_5877_ = lean_ctor_get(v___x_5876_, 0);
                    v_isSharedCheck_5891_ = (!lean_is_exclusive(v___x_5876_)) as u8;
                    if v_isSharedCheck_5891_ == 0 {
                        v___x_5879_ = v___x_5876_;
                        v_isShared_5880_ = v_isSharedCheck_5891_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5877_);
                        lean_dec(v___x_5876_);
                        v___x_5879_ = lean_box(0);
                        v_isShared_5880_ = v_isSharedCheck_5891_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_5892_ = lean_ctor_get(v___x_5876_, 0);
                    v_isSharedCheck_5899_ = (!lean_is_exclusive(v___x_5876_)) as u8;
                    if v_isSharedCheck_5899_ == 0 {
                        v___x_5894_ = v___x_5876_;
                        v_isShared_5895_ = v_isSharedCheck_5899_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5892_);
                        lean_dec(v___x_5876_);
                        v___x_5894_ = lean_box(0);
                        v_isShared_5895_ = v_isSharedCheck_5899_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_5881_ = lean_ctor_get(v_a_5877_, 0);
                lean_inc(v_fst_5881_);
                lean_dec(v_a_5877_);
                if lean_obj_tag(v_fst_5881_) == 0 {
                    v___x_5882_ = 0;
                    v___x_5883_ = lean_box((v___x_5882_) as usize);
                    if v_isShared_5880_ == 0 {
                        lean_ctor_set(v___x_5879_, 0, v___x_5883_);
                        v___x_5885_ = v___x_5879_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5886_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5886_, 0, v___x_5883_);
                        v___x_5885_ = v_reuseFailAlloc_5886_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_5887_ = lean_ctor_get(v_fst_5881_, 0);
                    lean_inc(v_val_5887_);
                    lean_dec_ref_known(v_fst_5881_, 1);
                    if v_isShared_5880_ == 0 {
                        lean_ctor_set(v___x_5879_, 0, v_val_5887_);
                        v___x_5889_ = v___x_5879_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5890_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5890_, 0, v_val_5887_);
                        v___x_5889_ = v_reuseFailAlloc_5890_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5885_;
            }
            4 => {
                return v___x_5889_;
            }
            5 => {
                if v_isShared_5895_ == 0 {
                    v___x_5897_ = v___x_5894_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5898_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5898_, 0, v_a_5892_);
                    v___x_5897_ = v_reuseFailAlloc_5898_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5897_;
            }
            7 => {
                if v_isShared_5917_ == 0 {
                    v___x_5919_ = v___x_5916_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5920_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5920_, 0, v_a_5914_);
                    v___x_5919_ = v_reuseFailAlloc_5920_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5919_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___boxed(
    mut v_c_5923_: *mut LeanObject,
    mut v_a_5924_: *mut LeanObject,
    mut v_a_5925_: *mut LeanObject,
    mut v_a_5926_: *mut LeanObject,
    mut v_a_5927_: *mut LeanObject,
    mut v_a_5928_: *mut LeanObject,
    mut v_a_5929_: *mut LeanObject,
    mut v_a_5930_: *mut LeanObject,
    mut v_a_5931_: *mut LeanObject,
    mut v_a_5932_: *mut LeanObject,
    mut v_a_5933_: *mut LeanObject,
    mut v_a_5934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5935_: *mut LeanObject = core::ptr::null_mut();
    v_res_5935_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_c_5923_, v_a_5924_, v_a_5925_, v_a_5926_, v_a_5927_, v_a_5928_, v_a_5929_, v_a_5930_, v_a_5931_, v_a_5932_, v_a_5933_);
    lean_dec(v_a_5933_);
    lean_dec_ref(v_a_5932_);
    lean_dec(v_a_5931_);
    lean_dec_ref(v_a_5930_);
    lean_dec(v_a_5929_);
    lean_dec_ref(v_a_5928_);
    lean_dec(v_a_5927_);
    lean_dec_ref(v_a_5926_);
    lean_dec(v_a_5925_);
    lean_dec(v_a_5924_);
    return v_res_5935_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(
    mut v___x_5936_: *mut LeanObject,
    mut v_as_5937_: *mut LeanObject,
    mut v_i_5938_: usize,
    mut v_stop_5939_: usize,
    mut v_b_5940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: usize = 0;
    let mut v___x_5944_: usize = 0;
    let mut v___x_5946_: u8 = 0;
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: u8 = 0;
    let mut v___x_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5946_ = lean_usize_dec_eq(v_i_5938_, v_stop_5939_);
                if v___x_5946_ == 0 {
                    v___x_5947_ = lean_array_uget_borrowed(v_as_5937_, v_i_5938_);
                    v_p_5948_ = lean_ctor_get(v___x_5947_, 0);
                    v___x_5949_ = l_Int_Linear_instBEqPoly_beq(v_p_5948_, v___x_5936_);
                    if v___x_5949_ == 0 {
                        lean_inc(v___x_5947_);
                        v___x_5950_ = l_Lean_PersistentArray_push___redArg(v_b_5940_, v___x_5947_);
                        v___y_5942_ = v___x_5950_;
                        state = 1;
                        continue;
                    } else {
                        v___y_5942_ = v_b_5940_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_5940_;
                }
            }
            1 => {
                v___x_5943_ = 1usize;
                v___x_5944_ = lean_usize_add(v_i_5938_, v___x_5943_);
                v_i_5938_ = v___x_5944_;
                v_b_5940_ = v___y_5942_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1___boxed(
    mut v___x_5951_: *mut LeanObject,
    mut v_as_5952_: *mut LeanObject,
    mut v_i_5953_: *mut LeanObject,
    mut v_stop_5954_: *mut LeanObject,
    mut v_b_5955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5956_: usize = 0;
    let mut v_stop_boxed_5957_: usize = 0;
    let mut v_res_5958_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5956_ = lean_unbox_usize(v_i_5953_);
    lean_dec(v_i_5953_);
    v_stop_boxed_5957_ = lean_unbox_usize(v_stop_5954_);
    lean_dec(v_stop_5954_);
    v_res_5958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_5951_, v_as_5952_, v_i_boxed_5956_, v_stop_boxed_5957_, v_b_5955_);
    lean_dec_ref(v_as_5952_);
    lean_dec_ref(v___x_5951_);
    return v_res_5958_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(
    mut v___x_5959_: *mut LeanObject,
    mut v_x_5960_: *mut LeanObject,
    mut v_x_5961_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5960_) == 0 {
        let mut v_cs_5962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5963_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5965_: u8 = 0;
        v_cs_5962_ = lean_ctor_get(v_x_5960_, 0);
        v___x_5963_ = lean_unsigned_to_nat(0);
        v___x_5964_ = lean_array_get_size(v_cs_5962_);
        v___x_5965_ = lean_nat_dec_lt(v___x_5963_, v___x_5964_);
        if v___x_5965_ == 0 {
            return v_x_5961_;
        } else {
            let mut v___x_5966_: u8 = 0;
            v___x_5966_ = lean_nat_dec_le(v___x_5964_, v___x_5964_);
            if v___x_5966_ == 0 {
                if v___x_5965_ == 0 {
                    return v_x_5961_;
                } else {
                    let mut v___x_5967_: usize = 0;
                    let mut v___x_5968_: usize = 0;
                    let mut v___x_5969_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5967_ = 0usize;
                    v___x_5968_ = lean_usize_of_nat(v___x_5964_);
                    v___x_5969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_5959_, v_cs_5962_, v___x_5967_, v___x_5968_, v_x_5961_);
                    return v___x_5969_;
                }
            } else {
                let mut v___x_5970_: usize = 0;
                let mut v___x_5971_: usize = 0;
                let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
                v___x_5970_ = 0usize;
                v___x_5971_ = lean_usize_of_nat(v___x_5964_);
                v___x_5972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_5959_, v_cs_5962_, v___x_5970_, v___x_5971_, v_x_5961_);
                return v___x_5972_;
            }
        }
    } else {
        let mut v_vs_5973_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5974_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5975_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5976_: u8 = 0;
        v_vs_5973_ = lean_ctor_get(v_x_5960_, 0);
        v___x_5974_ = lean_unsigned_to_nat(0);
        v___x_5975_ = lean_array_get_size(v_vs_5973_);
        v___x_5976_ = lean_nat_dec_lt(v___x_5974_, v___x_5975_);
        if v___x_5976_ == 0 {
            return v_x_5961_;
        } else {
            let mut v___x_5977_: u8 = 0;
            v___x_5977_ = lean_nat_dec_le(v___x_5975_, v___x_5975_);
            if v___x_5977_ == 0 {
                if v___x_5976_ == 0 {
                    return v_x_5961_;
                } else {
                    let mut v___x_5978_: usize = 0;
                    let mut v___x_5979_: usize = 0;
                    let mut v___x_5980_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5978_ = 0usize;
                    v___x_5979_ = lean_usize_of_nat(v___x_5975_);
                    v___x_5980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_5959_, v_vs_5973_, v___x_5978_, v___x_5979_, v_x_5961_);
                    return v___x_5980_;
                }
            } else {
                let mut v___x_5981_: usize = 0;
                let mut v___x_5982_: usize = 0;
                let mut v___x_5983_: *mut LeanObject = core::ptr::null_mut();
                v___x_5981_ = 0usize;
                v___x_5982_ = lean_usize_of_nat(v___x_5975_);
                v___x_5983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_5959_, v_vs_5973_, v___x_5981_, v___x_5982_, v_x_5961_);
                return v___x_5983_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(
    mut v___x_5984_: *mut LeanObject,
    mut v_as_5985_: *mut LeanObject,
    mut v_i_5986_: usize,
    mut v_stop_5987_: usize,
    mut v_b_5988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5989_: u8 = 0;
    let mut v___x_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: usize = 0;
    let mut v___x_5993_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5989_ = lean_usize_dec_eq(v_i_5986_, v_stop_5987_);
                if v___x_5989_ == 0 {
                    v___x_5990_ = lean_array_uget_borrowed(v_as_5985_, v_i_5986_);
                    v___x_5991_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_5984_, v___x_5990_, v_b_5988_);
                    v___x_5992_ = 1usize;
                    v___x_5993_ = lean_usize_add(v_i_5986_, v___x_5992_);
                    v_i_5986_ = v___x_5993_;
                    v_b_5988_ = v___x_5991_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5988_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1___boxed(
    mut v___x_5995_: *mut LeanObject,
    mut v_as_5996_: *mut LeanObject,
    mut v_i_5997_: *mut LeanObject,
    mut v_stop_5998_: *mut LeanObject,
    mut v_b_5999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6000_: usize = 0;
    let mut v_stop_boxed_6001_: usize = 0;
    let mut v_res_6002_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6000_ = lean_unbox_usize(v_i_5997_);
    lean_dec(v_i_5997_);
    v_stop_boxed_6001_ = lean_unbox_usize(v_stop_5998_);
    lean_dec(v_stop_5998_);
    v_res_6002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_5995_, v_as_5996_, v_i_boxed_6000_, v_stop_boxed_6001_, v_b_5999_);
    lean_dec_ref(v_as_5996_);
    lean_dec_ref(v___x_5995_);
    return v_res_6002_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2___boxed(
    mut v___x_6003_: *mut LeanObject,
    mut v_x_6004_: *mut LeanObject,
    mut v_x_6005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6006_: *mut LeanObject = core::ptr::null_mut();
    v_res_6006_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_6003_, v_x_6004_, v_x_6005_);
    lean_dec_ref(v_x_6004_);
    lean_dec_ref(v___x_6003_);
    return v_res_6006_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(
    mut v___x_6007_: *mut LeanObject,
    mut v_x_6008_: *mut LeanObject,
    mut v_x_6009_: usize,
    mut v_x_6010_: usize,
    mut v_x_6011_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6008_) == 0 {
        let mut v_cs_6012_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6013_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6014_: usize = 0;
        let mut v_j_6015_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6016_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6017_: usize = 0;
        let mut v___x_6018_: usize = 0;
        let mut v___x_6019_: usize = 0;
        let mut v___x_6020_: usize = 0;
        let mut v___x_6021_: usize = 0;
        let mut v___x_6022_: usize = 0;
        let mut v___x_6023_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6024_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6025_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6026_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6027_: u8 = 0;
        v_cs_6012_ = lean_ctor_get(v_x_6008_, 0);
        v___x_6013_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
        v___x_6014_ = lean_usize_shift_right(v_x_6009_, v_x_6010_);
        v_j_6015_ = lean_usize_to_nat(v___x_6014_);
        v___x_6016_ = lean_array_get_borrowed(v___x_6013_, v_cs_6012_, v_j_6015_);
        v___x_6017_ = 1usize;
        v___x_6018_ = lean_usize_shift_left(v___x_6017_, v_x_6010_);
        v___x_6019_ = lean_usize_sub(v___x_6018_, v___x_6017_);
        v___x_6020_ = lean_usize_land(v_x_6009_, v___x_6019_);
        v___x_6021_ = 5usize;
        v___x_6022_ = lean_usize_sub(v_x_6010_, v___x_6021_);
        v___x_6023_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_6007_, v___x_6016_, v___x_6020_, v___x_6022_, v_x_6011_);
        v___x_6024_ = lean_unsigned_to_nat(1);
        v___x_6025_ = lean_nat_add(v_j_6015_, v___x_6024_);
        lean_dec(v_j_6015_);
        v___x_6026_ = lean_array_get_size(v_cs_6012_);
        v___x_6027_ = lean_nat_dec_lt(v___x_6025_, v___x_6026_);
        if v___x_6027_ == 0 {
            lean_dec(v___x_6025_);
            return v___x_6023_;
        } else {
            let mut v___x_6028_: u8 = 0;
            v___x_6028_ = lean_nat_dec_le(v___x_6026_, v___x_6026_);
            if v___x_6028_ == 0 {
                if v___x_6027_ == 0 {
                    lean_dec(v___x_6025_);
                    return v___x_6023_;
                } else {
                    let mut v___x_6029_: usize = 0;
                    let mut v___x_6030_: usize = 0;
                    let mut v___x_6031_: *mut LeanObject = core::ptr::null_mut();
                    v___x_6029_ = lean_usize_of_nat(v___x_6025_);
                    lean_dec(v___x_6025_);
                    v___x_6030_ = lean_usize_of_nat(v___x_6026_);
                    v___x_6031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_6007_, v_cs_6012_, v___x_6029_, v___x_6030_, v___x_6023_);
                    return v___x_6031_;
                }
            } else {
                let mut v___x_6032_: usize = 0;
                let mut v___x_6033_: usize = 0;
                let mut v___x_6034_: *mut LeanObject = core::ptr::null_mut();
                v___x_6032_ = lean_usize_of_nat(v___x_6025_);
                lean_dec(v___x_6025_);
                v___x_6033_ = lean_usize_of_nat(v___x_6026_);
                v___x_6034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_6007_, v_cs_6012_, v___x_6032_, v___x_6033_, v___x_6023_);
                return v___x_6034_;
            }
        }
    } else {
        let mut v_vs_6035_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6036_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6037_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6038_: u8 = 0;
        v_vs_6035_ = lean_ctor_get(v_x_6008_, 0);
        v___x_6036_ = lean_usize_to_nat(v_x_6009_);
        v___x_6037_ = lean_array_get_size(v_vs_6035_);
        v___x_6038_ = lean_nat_dec_lt(v___x_6036_, v___x_6037_);
        if v___x_6038_ == 0 {
            lean_dec(v___x_6036_);
            return v_x_6011_;
        } else {
            let mut v___x_6039_: u8 = 0;
            v___x_6039_ = lean_nat_dec_le(v___x_6037_, v___x_6037_);
            if v___x_6039_ == 0 {
                if v___x_6038_ == 0 {
                    lean_dec(v___x_6036_);
                    return v_x_6011_;
                } else {
                    let mut v___x_6040_: usize = 0;
                    let mut v___x_6041_: usize = 0;
                    let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
                    v___x_6040_ = lean_usize_of_nat(v___x_6036_);
                    lean_dec(v___x_6036_);
                    v___x_6041_ = lean_usize_of_nat(v___x_6037_);
                    v___x_6042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_6007_, v_vs_6035_, v___x_6040_, v___x_6041_, v_x_6011_);
                    return v___x_6042_;
                }
            } else {
                let mut v___x_6043_: usize = 0;
                let mut v___x_6044_: usize = 0;
                let mut v___x_6045_: *mut LeanObject = core::ptr::null_mut();
                v___x_6043_ = lean_usize_of_nat(v___x_6036_);
                lean_dec(v___x_6036_);
                v___x_6044_ = lean_usize_of_nat(v___x_6037_);
                v___x_6045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_6007_, v_vs_6035_, v___x_6043_, v___x_6044_, v_x_6011_);
                return v___x_6045_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___boxed(
    mut v___x_6046_: *mut LeanObject,
    mut v_x_6047_: *mut LeanObject,
    mut v_x_6048_: *mut LeanObject,
    mut v_x_6049_: *mut LeanObject,
    mut v_x_6050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_21627__boxed_6051_: usize = 0;
    let mut v_x_21628__boxed_6052_: usize = 0;
    let mut v_res_6053_: *mut LeanObject = core::ptr::null_mut();
    v_x_21627__boxed_6051_ = lean_unbox_usize(v_x_6048_);
    lean_dec(v_x_6048_);
    v_x_21628__boxed_6052_ = lean_unbox_usize(v_x_6049_);
    lean_dec(v_x_6049_);
    v_res_6053_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_6046_, v_x_6047_, v_x_21627__boxed_6051_, v_x_21628__boxed_6052_, v_x_6050_);
    lean_dec_ref(v_x_6047_);
    lean_dec_ref(v___x_6046_);
    return v_res_6053_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(
    mut v___x_6054_: *mut LeanObject,
    mut v_t_6055_: *mut LeanObject,
    mut v_init_6056_: *mut LeanObject,
    mut v_start_6057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: u8 = 0;
    v___x_6058_ = lean_unsigned_to_nat(0);
    v___x_6059_ = lean_nat_dec_eq(v_start_6057_, v___x_6058_);
    if v___x_6059_ == 0 {
        let mut v_root_6060_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_6061_: *mut LeanObject = core::ptr::null_mut();
        let mut v_shift_6062_: usize = 0;
        let mut v_tailOff_6063_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6064_: u8 = 0;
        v_root_6060_ = lean_ctor_get(v_t_6055_, 0);
        v_tail_6061_ = lean_ctor_get(v_t_6055_, 1);
        v_shift_6062_ = lean_ctor_get_usize(v_t_6055_, 4);
        v_tailOff_6063_ = lean_ctor_get(v_t_6055_, 3);
        v___x_6064_ = lean_nat_dec_le(v_tailOff_6063_, v_start_6057_);
        if v___x_6064_ == 0 {
            let mut v___x_6065_: usize = 0;
            let mut v___x_6066_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6068_: u8 = 0;
            v___x_6065_ = lean_usize_of_nat(v_start_6057_);
            v___x_6066_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_6054_, v_root_6060_, v___x_6065_, v_shift_6062_, v_init_6056_);
            v___x_6067_ = lean_array_get_size(v_tail_6061_);
            v___x_6068_ = lean_nat_dec_lt(v___x_6058_, v___x_6067_);
            if v___x_6068_ == 0 {
                return v___x_6066_;
            } else {
                let mut v___x_6069_: u8 = 0;
                v___x_6069_ = lean_nat_dec_le(v___x_6067_, v___x_6067_);
                if v___x_6069_ == 0 {
                    if v___x_6068_ == 0 {
                        return v___x_6066_;
                    } else {
                        let mut v___x_6070_: usize = 0;
                        let mut v___x_6071_: usize = 0;
                        let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
                        v___x_6070_ = 0usize;
                        v___x_6071_ = lean_usize_of_nat(v___x_6067_);
                        v___x_6072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_6054_, v_tail_6061_, v___x_6070_, v___x_6071_, v___x_6066_);
                        return v___x_6072_;
                    }
                } else {
                    let mut v___x_6073_: usize = 0;
                    let mut v___x_6074_: usize = 0;
                    let mut v___x_6075_: *mut LeanObject = core::ptr::null_mut();
                    v___x_6073_ = 0usize;
                    v___x_6074_ = lean_usize_of_nat(v___x_6067_);
                    v___x_6075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_6054_, v_tail_6061_, v___x_6073_, v___x_6074_, v___x_6066_);
                    return v___x_6075_;
                }
            }
        } else {
            let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6077_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6078_: u8 = 0;
            v___x_6076_ = lean_nat_sub(v_start_6057_, v_tailOff_6063_);
            v___x_6077_ = lean_array_get_size(v_tail_6061_);
            v___x_6078_ = lean_nat_dec_lt(v___x_6076_, v___x_6077_);
            if v___x_6078_ == 0 {
                lean_dec(v___x_6076_);
                return v_init_6056_;
            } else {
                let mut v___x_6079_: u8 = 0;
                v___x_6079_ = lean_nat_dec_le(v___x_6077_, v___x_6077_);
                if v___x_6079_ == 0 {
                    if v___x_6078_ == 0 {
                        lean_dec(v___x_6076_);
                        return v_init_6056_;
                    } else {
                        let mut v___x_6080_: usize = 0;
                        let mut v___x_6081_: usize = 0;
                        let mut v___x_6082_: *mut LeanObject = core::ptr::null_mut();
                        v___x_6080_ = lean_usize_of_nat(v___x_6076_);
                        lean_dec(v___x_6076_);
                        v___x_6081_ = lean_usize_of_nat(v___x_6077_);
                        v___x_6082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_6054_, v_tail_6061_, v___x_6080_, v___x_6081_, v_init_6056_);
                        return v___x_6082_;
                    }
                } else {
                    let mut v___x_6083_: usize = 0;
                    let mut v___x_6084_: usize = 0;
                    let mut v___x_6085_: *mut LeanObject = core::ptr::null_mut();
                    v___x_6083_ = lean_usize_of_nat(v___x_6076_);
                    lean_dec(v___x_6076_);
                    v___x_6084_ = lean_usize_of_nat(v___x_6077_);
                    v___x_6085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_6054_, v_tail_6061_, v___x_6083_, v___x_6084_, v_init_6056_);
                    return v___x_6085_;
                }
            }
        }
    } else {
        let mut v_root_6086_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_6087_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6088_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6089_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6090_: u8 = 0;
        v_root_6086_ = lean_ctor_get(v_t_6055_, 0);
        v_tail_6087_ = lean_ctor_get(v_t_6055_, 1);
        v___x_6088_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_6054_, v_root_6086_, v_init_6056_);
        v___x_6089_ = lean_array_get_size(v_tail_6087_);
        v___x_6090_ = lean_nat_dec_lt(v___x_6058_, v___x_6089_);
        if v___x_6090_ == 0 {
            return v___x_6088_;
        } else {
            let mut v___x_6091_: u8 = 0;
            v___x_6091_ = lean_nat_dec_le(v___x_6089_, v___x_6089_);
            if v___x_6091_ == 0 {
                if v___x_6090_ == 0 {
                    return v___x_6088_;
                } else {
                    let mut v___x_6092_: usize = 0;
                    let mut v___x_6093_: usize = 0;
                    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
                    v___x_6092_ = 0usize;
                    v___x_6093_ = lean_usize_of_nat(v___x_6089_);
                    v___x_6094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_6054_, v_tail_6087_, v___x_6092_, v___x_6093_, v___x_6088_);
                    return v___x_6094_;
                }
            } else {
                let mut v___x_6095_: usize = 0;
                let mut v___x_6096_: usize = 0;
                let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
                v___x_6095_ = 0usize;
                v___x_6096_ = lean_usize_of_nat(v___x_6089_);
                v___x_6097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_6054_, v_tail_6087_, v___x_6095_, v___x_6096_, v___x_6088_);
                return v___x_6097_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0___boxed(
    mut v___x_6098_: *mut LeanObject,
    mut v_t_6099_: *mut LeanObject,
    mut v_init_6100_: *mut LeanObject,
    mut v_start_6101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6102_: *mut LeanObject = core::ptr::null_mut();
    v_res_6102_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_6098_, v_t_6099_, v_init_6100_, v_start_6101_);
    lean_dec(v_start_6101_);
    lean_dec_ref(v_t_6099_);
    lean_dec_ref(v___x_6098_);
    return v_res_6102_;
}
pub unsafe fn _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0()
-> *mut LeanObject {
    let mut v___x_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut LeanObject = core::ptr::null_mut();
    v___x_6103_ = lean_unsigned_to_nat(32);
    v___x_6104_ = lean_mk_empty_array_with_capacity(v___x_6103_);
    v___x_6105_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6105_, 0, v___x_6104_);
    return v___x_6105_;
}
pub unsafe fn _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1()
-> *mut LeanObject {
    let mut v___x_6106_: usize = 0;
    let mut v___x_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6111_: *mut LeanObject = core::ptr::null_mut();
    v___x_6106_ = 5usize;
    v___x_6107_ = lean_unsigned_to_nat(0);
    v___x_6108_ = lean_unsigned_to_nat(32);
    v___x_6109_ = lean_mk_empty_array_with_capacity(v___x_6108_);
    v___x_6110_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0_once), _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0);
    v___x_6111_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_6111_, 0, v___x_6110_);
    lean_ctor_set(v___x_6111_, 1, v___x_6109_);
    lean_ctor_set(v___x_6111_, 2, v___x_6107_);
    lean_ctor_set(v___x_6111_, 3, v___x_6107_);
    lean_ctor_set_usize(v___x_6111_, 4, v___x_6106_);
    return v___x_6111_;
}
pub unsafe fn l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(
    mut v___x_6112_: *mut LeanObject,
    mut v_x_6113_: *mut LeanObject,
    mut v_x_6114_: usize,
    mut v_x_6115_: usize,
) -> *mut LeanObject {
    let mut v_cs_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_6117_: usize = 0;
    let mut v___x_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: u8 = 0;
    let mut v___x_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6123_: u8 = 0;
    let mut v___x_6124_: usize = 0;
    let mut v___x_6125_: usize = 0;
    let mut v___x_6126_: usize = 0;
    let mut v_i_6127_: usize = 0;
    let mut v___x_6128_: usize = 0;
    let mut v_shift_6129_: usize = 0;
    let mut v_v_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6138_: u8 = 0;
    let mut v_unused_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: u8 = 0;
    let mut v___x_6145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6146_: u8 = 0;
    let mut v_v_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_6149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6157_: u8 = 0;
    let mut v_unused_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6113_) == 0 {
                    v_cs_6116_ = lean_ctor_get(v_x_6113_, 0);
                    v_j_6117_ = lean_usize_shift_right(v_x_6114_, v_x_6115_);
                    v___x_6118_ = lean_usize_to_nat(v_j_6117_);
                    v___x_6119_ = lean_array_get_size(v_cs_6116_);
                    v___x_6120_ = lean_nat_dec_lt(v___x_6118_, v___x_6119_);
                    if v___x_6120_ == 0 {
                        lean_dec(v___x_6118_);
                        return v_x_6113_;
                    } else {
                        lean_inc_ref(v_cs_6116_);
                        v_isSharedCheck_6138_ = (!lean_is_exclusive(v_x_6113_)) as u8;
                        if v_isSharedCheck_6138_ == 0 {
                            v_unused_6139_ = lean_ctor_get(v_x_6113_, 0);
                            lean_dec(v_unused_6139_);
                            v___x_6122_ = v_x_6113_;
                            v_isShared_6123_ = v_isSharedCheck_6138_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_6113_);
                            v___x_6122_ = lean_box(0);
                            v_isShared_6123_ = v_isSharedCheck_6138_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_vs_6140_ = lean_ctor_get(v_x_6113_, 0);
                    v___x_6141_ = lean_usize_to_nat(v_x_6114_);
                    v___x_6142_ = lean_array_get_size(v_vs_6140_);
                    v___x_6143_ = lean_nat_dec_lt(v___x_6141_, v___x_6142_);
                    if v___x_6143_ == 0 {
                        lean_dec(v___x_6141_);
                        return v_x_6113_;
                    } else {
                        lean_inc_ref(v_vs_6140_);
                        v_isSharedCheck_6157_ = (!lean_is_exclusive(v_x_6113_)) as u8;
                        if v_isSharedCheck_6157_ == 0 {
                            v_unused_6158_ = lean_ctor_get(v_x_6113_, 0);
                            lean_dec(v_unused_6158_);
                            v___x_6145_ = v_x_6113_;
                            v_isShared_6146_ = v_isSharedCheck_6157_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v_x_6113_);
                            v___x_6145_ = lean_box(0);
                            v_isShared_6146_ = v_isSharedCheck_6157_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6124_ = 1usize;
                v___x_6125_ = lean_usize_shift_left(v___x_6124_, v_x_6115_);
                v___x_6126_ = lean_usize_sub(v___x_6125_, v___x_6124_);
                v_i_6127_ = lean_usize_land(v_x_6114_, v___x_6126_);
                v___x_6128_ = 5usize;
                v_shift_6129_ = lean_usize_sub(v_x_6115_, v___x_6128_);
                v_v_6130_ = lean_array_fget(v_cs_6116_, v___x_6118_);
                v___x_6131_ = lean_box(0);
                v_xs_x27_6132_ = lean_array_fset(v_cs_6116_, v___x_6118_, v___x_6131_);
                v___x_6133_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_6112_, v_v_6130_, v_i_6127_, v_shift_6129_);
                v___x_6134_ = lean_array_fset(v_xs_x27_6132_, v___x_6118_, v___x_6133_);
                lean_dec(v___x_6118_);
                if v_isShared_6123_ == 0 {
                    lean_ctor_set(v___x_6122_, 0, v___x_6134_);
                    v___x_6136_ = v___x_6122_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6137_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6137_, 0, v___x_6134_);
                    v___x_6136_ = v_reuseFailAlloc_6137_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6136_;
            }
            3 => {
                v_v_6147_ = lean_array_fget(v_vs_6140_, v___x_6141_);
                v___x_6148_ = lean_box(0);
                v_xs_x27_6149_ = lean_array_fset(v_vs_6140_, v___x_6141_, v___x_6148_);
                v___x_6150_ = lean_unsigned_to_nat(0);
                v___x_6151_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once), _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
                v___x_6152_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_6112_, v_v_6147_, v___x_6151_, v___x_6150_);
                lean_dec(v_v_6147_);
                v___x_6153_ = lean_array_fset(v_xs_x27_6149_, v___x_6141_, v___x_6152_);
                lean_dec(v___x_6141_);
                if v_isShared_6146_ == 0 {
                    lean_ctor_set(v___x_6145_, 0, v___x_6153_);
                    v___x_6155_ = v___x_6145_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6156_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6156_, 0, v___x_6153_);
                    v___x_6155_ = v_reuseFailAlloc_6156_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6155_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___boxed(
    mut v___x_6159_: *mut LeanObject,
    mut v_x_6160_: *mut LeanObject,
    mut v_x_6161_: *mut LeanObject,
    mut v_x_6162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_21799__boxed_6163_: usize = 0;
    let mut v_x_21800__boxed_6164_: usize = 0;
    let mut v_res_6165_: *mut LeanObject = core::ptr::null_mut();
    v_x_21799__boxed_6163_ = lean_unbox_usize(v_x_6161_);
    lean_dec(v_x_6161_);
    v_x_21800__boxed_6164_ = lean_unbox_usize(v_x_6162_);
    lean_dec(v_x_6162_);
    v_res_6165_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_6159_, v_x_6160_, v_x_21799__boxed_6163_, v_x_21800__boxed_6164_);
    lean_dec_ref(v___x_6159_);
    return v_res_6165_;
}
pub unsafe fn l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(
    mut v___x_6166_: *mut LeanObject,
    mut v_t_6167_: *mut LeanObject,
    mut v_i_6168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_6172_: usize = 0;
    let mut v_tailOff_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6176_: u8 = 0;
    let mut v___x_6177_: u8 = 0;
    let mut v___x_6178_: usize = 0;
    let mut v___x_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: u8 = 0;
    let mut v___x_6187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6201_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_6169_ = lean_ctor_get(v_t_6167_, 0);
                v_tail_6170_ = lean_ctor_get(v_t_6167_, 1);
                v_size_6171_ = lean_ctor_get(v_t_6167_, 2);
                v_shift_6172_ = lean_ctor_get_usize(v_t_6167_, 4);
                v_tailOff_6173_ = lean_ctor_get(v_t_6167_, 3);
                v_isSharedCheck_6201_ = (!lean_is_exclusive(v_t_6167_)) as u8;
                if v_isSharedCheck_6201_ == 0 {
                    v___x_6175_ = v_t_6167_;
                    v_isShared_6176_ = v_isSharedCheck_6201_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_tailOff_6173_);
                    lean_inc(v_size_6171_);
                    lean_inc(v_tail_6170_);
                    lean_inc(v_root_6169_);
                    lean_dec(v_t_6167_);
                    v___x_6175_ = lean_box(0);
                    v_isShared_6176_ = v_isSharedCheck_6201_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6177_ = lean_nat_dec_le(v_tailOff_6173_, v_i_6168_);
                if v___x_6177_ == 0 {
                    v___x_6178_ = lean_usize_of_nat(v_i_6168_);
                    v___x_6179_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_6166_, v_root_6169_, v___x_6178_, v_shift_6172_);
                    if v_isShared_6176_ == 0 {
                        lean_ctor_set(v___x_6175_, 0, v___x_6179_);
                        v___x_6181_ = v___x_6175_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6182_ =
                            lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6182_, 0, v___x_6179_);
                        lean_ctor_set(v_reuseFailAlloc_6182_, 1, v_tail_6170_);
                        lean_ctor_set(v_reuseFailAlloc_6182_, 2, v_size_6171_);
                        lean_ctor_set(v_reuseFailAlloc_6182_, 3, v_tailOff_6173_);
                        lean_ctor_set_usize(v_reuseFailAlloc_6182_, 4, v_shift_6172_);
                        v___x_6181_ = v_reuseFailAlloc_6182_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6183_ = lean_nat_sub(v_i_6168_, v_tailOff_6173_);
                    v___x_6184_ = lean_array_get_size(v_tail_6170_);
                    v___x_6185_ = lean_nat_dec_lt(v___x_6183_, v___x_6184_);
                    if v___x_6185_ == 0 {
                        lean_dec(v___x_6183_);
                        if v_isShared_6176_ == 0 {
                            v___x_6187_ = v___x_6175_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6188_ =
                                lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6188_, 0, v_root_6169_);
                            lean_ctor_set(v_reuseFailAlloc_6188_, 1, v_tail_6170_);
                            lean_ctor_set(v_reuseFailAlloc_6188_, 2, v_size_6171_);
                            lean_ctor_set(v_reuseFailAlloc_6188_, 3, v_tailOff_6173_);
                            lean_ctor_set_usize(v_reuseFailAlloc_6188_, 4, v_shift_6172_);
                            v___x_6187_ = v_reuseFailAlloc_6188_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_v_6189_ = lean_array_fget(v_tail_6170_, v___x_6183_);
                        v___x_6190_ = lean_box(0);
                        v_xs_x27_6191_ = lean_array_fset(v_tail_6170_, v___x_6183_, v___x_6190_);
                        v___x_6192_ = lean_unsigned_to_nat(32);
                        v___x_6193_ = lean_mk_empty_array_with_capacity(v___x_6192_);
                        lean_dec_ref(v___x_6193_);
                        v___x_6194_ = lean_unsigned_to_nat(0);
                        v___x_6195_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once), _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
                        v___x_6196_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_6166_, v_v_6189_, v___x_6195_, v___x_6194_);
                        lean_dec(v_v_6189_);
                        v___x_6197_ = lean_array_fset(v_xs_x27_6191_, v___x_6183_, v___x_6196_);
                        lean_dec(v___x_6183_);
                        if v_isShared_6176_ == 0 {
                            lean_ctor_set(v___x_6175_, 1, v___x_6197_);
                            v___x_6199_ = v___x_6175_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6200_ =
                                lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6200_, 0, v_root_6169_);
                            lean_ctor_set(v_reuseFailAlloc_6200_, 1, v___x_6197_);
                            lean_ctor_set(v_reuseFailAlloc_6200_, 2, v_size_6171_);
                            lean_ctor_set(v_reuseFailAlloc_6200_, 3, v_tailOff_6173_);
                            lean_ctor_set_usize(v_reuseFailAlloc_6200_, 4, v_shift_6172_);
                            v___x_6199_ = v_reuseFailAlloc_6200_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_6181_;
            }
            3 => {
                return v___x_6187_;
            }
            4 => {
                return v___x_6199_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1___boxed(
    mut v___x_6202_: *mut LeanObject,
    mut v_t_6203_: *mut LeanObject,
    mut v_i_6204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6205_: *mut LeanObject = core::ptr::null_mut();
    v_res_6205_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v___x_6202_, v_t_6203_, v_i_6204_);
    lean_dec(v_i_6204_);
    lean_dec_ref(v___x_6202_);
    return v_res_6205_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(
    mut v_p_6206_: *mut LeanObject,
    mut v_x_6207_: *mut LeanObject,
    mut v_s_6208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vars_6209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_x27_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_x27_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natDef_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dvds_6215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowers_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uppers_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_occurs_6221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_6222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextCnstrId_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_6224_: u8 = 0;
    let mut v_conflict_x3f_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_divMod_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntIds_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntInfos_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedCommRing_6232_: u8 = 0;
    let mut v_nonlinearOccs_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6236_: u8 = 0;
    let mut v___x_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_6209_ = lean_ctor_get(v_s_6208_, 0);
                v_varMap_6210_ = lean_ctor_get(v_s_6208_, 1);
                v_vars_x27_6211_ = lean_ctor_get(v_s_6208_, 2);
                v_varMap_x27_6212_ = lean_ctor_get(v_s_6208_, 3);
                v_natToIntMap_6213_ = lean_ctor_get(v_s_6208_, 4);
                v_natDef_6214_ = lean_ctor_get(v_s_6208_, 5);
                v_dvds_6215_ = lean_ctor_get(v_s_6208_, 6);
                v_lowers_6216_ = lean_ctor_get(v_s_6208_, 7);
                v_uppers_6217_ = lean_ctor_get(v_s_6208_, 8);
                v_diseqs_6218_ = lean_ctor_get(v_s_6208_, 9);
                v_elimEqs_6219_ = lean_ctor_get(v_s_6208_, 10);
                v_elimStack_6220_ = lean_ctor_get(v_s_6208_, 11);
                v_occurs_6221_ = lean_ctor_get(v_s_6208_, 12);
                v_assignment_6222_ = lean_ctor_get(v_s_6208_, 13);
                v_nextCnstrId_6223_ = lean_ctor_get(v_s_6208_, 14);
                v_caseSplits_6224_ = lean_ctor_get_uint8(
                    v_s_6208_,
                    (core::mem::size_of::<*mut LeanObject>() * 23) as u32,
                );
                v_conflict_x3f_6225_ = lean_ctor_get(v_s_6208_, 15);
                v_diseqSplits_6226_ = lean_ctor_get(v_s_6208_, 16);
                v_divMod_6227_ = lean_ctor_get(v_s_6208_, 17);
                v_toIntIds_6228_ = lean_ctor_get(v_s_6208_, 18);
                v_toIntInfos_6229_ = lean_ctor_get(v_s_6208_, 19);
                v_toIntTermMap_6230_ = lean_ctor_get(v_s_6208_, 20);
                v_toIntVarMap_6231_ = lean_ctor_get(v_s_6208_, 21);
                v_usedCommRing_6232_ = lean_ctor_get_uint8(
                    v_s_6208_,
                    (core::mem::size_of::<*mut LeanObject>() * 23 + 1) as u32,
                );
                v_nonlinearOccs_6233_ = lean_ctor_get(v_s_6208_, 22);
                v_isSharedCheck_6241_ = (!lean_is_exclusive(v_s_6208_)) as u8;
                if v_isSharedCheck_6241_ == 0 {
                    v___x_6235_ = v_s_6208_;
                    v_isShared_6236_ = v_isSharedCheck_6241_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nonlinearOccs_6233_);
                    lean_inc(v_toIntVarMap_6231_);
                    lean_inc(v_toIntTermMap_6230_);
                    lean_inc(v_toIntInfos_6229_);
                    lean_inc(v_toIntIds_6228_);
                    lean_inc(v_divMod_6227_);
                    lean_inc(v_diseqSplits_6226_);
                    lean_inc(v_conflict_x3f_6225_);
                    lean_inc(v_nextCnstrId_6223_);
                    lean_inc(v_assignment_6222_);
                    lean_inc(v_occurs_6221_);
                    lean_inc(v_elimStack_6220_);
                    lean_inc(v_elimEqs_6219_);
                    lean_inc(v_diseqs_6218_);
                    lean_inc(v_uppers_6217_);
                    lean_inc(v_lowers_6216_);
                    lean_inc(v_dvds_6215_);
                    lean_inc(v_natDef_6214_);
                    lean_inc(v_natToIntMap_6213_);
                    lean_inc(v_varMap_x27_6212_);
                    lean_inc(v_vars_x27_6211_);
                    lean_inc(v_varMap_6210_);
                    lean_inc(v_vars_6209_);
                    lean_dec(v_s_6208_);
                    v___x_6235_ = lean_box(0);
                    v_isShared_6236_ = v_isSharedCheck_6241_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6237_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v_p_6206_, v_diseqs_6218_, v_x_6207_);
                if v_isShared_6236_ == 0 {
                    lean_ctor_set(v___x_6235_, 9, v___x_6237_);
                    v___x_6239_ = v___x_6235_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6240_ = lean_alloc_ctor(0, 23, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 0, v_vars_6209_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 1, v_varMap_6210_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 2, v_vars_x27_6211_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 3, v_varMap_x27_6212_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 4, v_natToIntMap_6213_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 5, v_natDef_6214_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 6, v_dvds_6215_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 7, v_lowers_6216_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 8, v_uppers_6217_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 9, v___x_6237_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 10, v_elimEqs_6219_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 11, v_elimStack_6220_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 12, v_occurs_6221_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 13, v_assignment_6222_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 14, v_nextCnstrId_6223_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 15, v_conflict_x3f_6225_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 16, v_diseqSplits_6226_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 17, v_divMod_6227_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 18, v_toIntIds_6228_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 19, v_toIntInfos_6229_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 20, v_toIntTermMap_6230_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 21, v_toIntVarMap_6231_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 22, v_nonlinearOccs_6233_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6240_,
                        (core::mem::size_of::<*mut LeanObject>() * 23) as u32,
                        v_caseSplits_6224_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6240_,
                        (core::mem::size_of::<*mut LeanObject>() * 23 + 1) as u32,
                        v_usedCommRing_6232_,
                    );
                    v___x_6239_ = v_reuseFailAlloc_6240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed(
    mut v_p_6242_: *mut LeanObject,
    mut v_x_6243_: *mut LeanObject,
    mut v_s_6244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6245_: *mut LeanObject = core::ptr::null_mut();
    v_res_6245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(v_p_6242_, v_x_6243_, v_s_6244_);
    lean_dec(v_x_6243_);
    lean_dec_ref(v_p_6242_);
    return v_res_6245_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut LeanObject = core::ptr::null_mut();
    v___x_6252_ = lean_unsigned_to_nat(1);
    v___x_6253_ = lean_nat_to_int(v___x_6252_);
    return v___x_6253_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(
    mut v_c_6254_: *mut LeanObject,
    mut v_x_6255_: *mut LeanObject,
    mut v_as_6256_: *mut LeanObject,
    mut v_sz_6257_: usize,
    mut v_i_6258_: usize,
    mut v_b_6259_: *mut LeanObject,
    mut v___y_6260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6262_: u8 = 0;
    let mut v___x_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6267_: u8 = 0;
    let mut v_p_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6274_: u8 = 0;
    let mut v___x_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: usize = 0;
    let mut v___x_6277_: usize = 0;
    let mut v___x_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6283_: u8 = 0;
    let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6298_: u8 = 0;
    let mut v_unused_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6303_: u8 = 0;
    let mut v___x_6305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6307_: u8 = 0;
    let mut v___x_6308_: u8 = 0;
    let mut v___x_6309_: u8 = 0;
    let mut v_isSharedCheck_6310_: u8 = 0;
    let mut v_unused_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6262_ = lean_usize_dec_lt(v_i_6258_, v_sz_6257_);
                if v___x_6262_ == 0 {
                    lean_dec(v_x_6255_);
                    lean_dec_ref(v_c_6254_);
                    v___x_6263_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6263_, 0, v_b_6259_);
                    return v___x_6263_;
                } else {
                    v_snd_6264_ = lean_ctor_get(v_b_6259_, 1);
                    v_isSharedCheck_6310_ = (!lean_is_exclusive(v_b_6259_)) as u8;
                    if v_isSharedCheck_6310_ == 0 {
                        v_unused_6311_ = lean_ctor_get(v_b_6259_, 0);
                        lean_dec(v_unused_6311_);
                        v___x_6266_ = v_b_6259_;
                        v_isShared_6267_ = v_isSharedCheck_6310_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6264_);
                        lean_dec(v_b_6259_);
                        v___x_6266_ = lean_box(0);
                        v_isShared_6267_ = v_isSharedCheck_6310_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_p_6268_ = lean_ctor_get(v_c_6254_, 0);
                v_a_6269_ = lean_array_uget_borrowed(v_as_6256_, v_i_6258_);
                v_p_6270_ = lean_ctor_get(v_a_6269_, 0);
                v___x_6271_ = lean_box(0);
                lean_inc(v_x_6255_);
                lean_inc_ref(v_p_6270_);
                v___f_6272_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                lean_closure_set(v___f_6272_, 0, v_p_6270_);
                lean_closure_set(v___f_6272_, 1, v_x_6255_);
                v___x_6308_ = l_Int_Linear_instBEqPoly_beq(v_p_6268_, v_p_6270_);
                if v___x_6308_ == 0 {
                    v___x_6309_ = l_Int_Linear_Poly_isNegEq(v_p_6268_, v_p_6270_);
                    v___y_6274_ = v___x_6309_;
                    state = 2;
                    continue;
                } else {
                    v___y_6274_ = v___x_6308_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_6274_ == 0 {
                    lean_dec_ref(v___f_6272_);
                    lean_del_object(v___x_6266_);
                    lean_dec(v_snd_6264_);
                    v___x_6275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1;
                    v___x_6276_ = 1usize;
                    v___x_6277_ = lean_usize_add(v_i_6258_, v___x_6276_);
                    v_i_6258_ = v___x_6277_;
                    v_b_6259_ = v___x_6275_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_x_6255_);
                    v___x_6279_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                    v___x_6280_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_6279_, v___f_6272_, v___y_6260_);
                    if lean_obj_tag(v___x_6280_) == 0 {
                        v_isSharedCheck_6298_ = (!lean_is_exclusive(v___x_6280_)) as u8;
                        if v_isSharedCheck_6298_ == 0 {
                            v_unused_6299_ = lean_ctor_get(v___x_6280_, 0);
                            lean_dec(v_unused_6299_);
                            v___x_6282_ = v___x_6280_;
                            v_isShared_6283_ = v_isSharedCheck_6298_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_6280_);
                            v___x_6282_ = lean_box(0);
                            v_isShared_6283_ = v_isSharedCheck_6298_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_6266_);
                        lean_dec(v_snd_6264_);
                        lean_dec_ref(v_c_6254_);
                        v_a_6300_ = lean_ctor_get(v___x_6280_, 0);
                        v_isSharedCheck_6307_ = (!lean_is_exclusive(v___x_6280_)) as u8;
                        if v_isSharedCheck_6307_ == 0 {
                            v___x_6302_ = v___x_6280_;
                            v_isShared_6303_ = v_isSharedCheck_6307_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6300_);
                            lean_dec(v___x_6280_);
                            v___x_6302_ = lean_box(0);
                            v_isShared_6303_ = v_isSharedCheck_6307_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_6284_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
                lean_inc_ref(v_p_6268_);
                v___x_6285_ = l_Int_Linear_Poly_addConst(v_p_6268_, v___x_6284_);
                lean_inc(v_a_6269_);
                v___x_6286_ = lean_alloc_ctor(11, 2, (0) as u32);
                lean_ctor_set(v___x_6286_, 0, v_c_6254_);
                lean_ctor_set(v___x_6286_, 1, v_a_6269_);
                v___x_6287_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6287_, 0, v___x_6285_);
                lean_ctor_set(v___x_6287_, 1, v___x_6286_);
                v___x_6288_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6288_, 0, v___x_6287_);
                v___x_6289_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6289_, 0, v___x_6288_);
                if v_isShared_6267_ == 0 {
                    lean_ctor_set(v___x_6266_, 1, v___x_6271_);
                    lean_ctor_set(v___x_6266_, 0, v___x_6289_);
                    v___x_6291_ = v___x_6266_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6297_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6297_, 0, v___x_6289_);
                    lean_ctor_set(v_reuseFailAlloc_6297_, 1, v___x_6271_);
                    v___x_6291_ = v_reuseFailAlloc_6297_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6292_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6292_, 0, v___x_6291_);
                v___x_6293_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6293_, 0, v___x_6292_);
                lean_ctor_set(v___x_6293_, 1, v_snd_6264_);
                if v_isShared_6283_ == 0 {
                    lean_ctor_set(v___x_6282_, 0, v___x_6293_);
                    v___x_6295_ = v___x_6282_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6296_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6296_, 0, v___x_6293_);
                    v___x_6295_ = v_reuseFailAlloc_6296_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6295_;
            }
            6 => {
                if v_isShared_6303_ == 0 {
                    v___x_6305_ = v___x_6302_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6306_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6306_, 0, v_a_6300_);
                    v___x_6305_ = v_reuseFailAlloc_6306_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___boxed(
    mut v_c_6312_: *mut LeanObject,
    mut v_x_6313_: *mut LeanObject,
    mut v_as_6314_: *mut LeanObject,
    mut v_sz_6315_: *mut LeanObject,
    mut v_i_6316_: *mut LeanObject,
    mut v_b_6317_: *mut LeanObject,
    mut v___y_6318_: *mut LeanObject,
    mut v___y_6319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6320_: usize = 0;
    let mut v_i_boxed_6321_: usize = 0;
    let mut v_res_6322_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6320_ = lean_unbox_usize(v_sz_6315_);
    lean_dec(v_sz_6315_);
    v_i_boxed_6321_ = lean_unbox_usize(v_i_6316_);
    lean_dec(v_i_6316_);
    v_res_6322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_6312_, v_x_6313_, v_as_6314_, v_sz_boxed_6320_, v_i_boxed_6321_, v_b_6317_, v___y_6318_);
    lean_dec(v___y_6318_);
    lean_dec_ref(v_as_6314_);
    return v_res_6322_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(
    mut v_c_6329_: *mut LeanObject,
    mut v_x_6330_: *mut LeanObject,
    mut v_as_6331_: *mut LeanObject,
    mut v_sz_6332_: usize,
    mut v_i_6333_: usize,
    mut v_b_6334_: *mut LeanObject,
    mut v___y_6335_: *mut LeanObject,
    mut v___y_6336_: *mut LeanObject,
    mut v___y_6337_: *mut LeanObject,
    mut v___y_6338_: *mut LeanObject,
    mut v___y_6339_: *mut LeanObject,
    mut v___y_6340_: *mut LeanObject,
    mut v___y_6341_: *mut LeanObject,
    mut v___y_6342_: *mut LeanObject,
    mut v___y_6343_: *mut LeanObject,
    mut v___y_6344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6346_: u8 = 0;
    let mut v___x_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6351_: u8 = 0;
    let mut v_p_6352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6358_: u8 = 0;
    let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: usize = 0;
    let mut v___x_6361_: usize = 0;
    let mut v___x_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6367_: u8 = 0;
    let mut v___x_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6382_: u8 = 0;
    let mut v_unused_6383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6387_: u8 = 0;
    let mut v___x_6389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6391_: u8 = 0;
    let mut v___x_6392_: u8 = 0;
    let mut v___x_6393_: u8 = 0;
    let mut v_isSharedCheck_6394_: u8 = 0;
    let mut v_unused_6395_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6346_ = lean_usize_dec_lt(v_i_6333_, v_sz_6332_);
                if v___x_6346_ == 0 {
                    lean_dec(v_x_6330_);
                    lean_dec_ref(v_c_6329_);
                    v___x_6347_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6347_, 0, v_b_6334_);
                    return v___x_6347_;
                } else {
                    v_snd_6348_ = lean_ctor_get(v_b_6334_, 1);
                    v_isSharedCheck_6394_ = (!lean_is_exclusive(v_b_6334_)) as u8;
                    if v_isSharedCheck_6394_ == 0 {
                        v_unused_6395_ = lean_ctor_get(v_b_6334_, 0);
                        lean_dec(v_unused_6395_);
                        v___x_6350_ = v_b_6334_;
                        v_isShared_6351_ = v_isSharedCheck_6394_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6348_);
                        lean_dec(v_b_6334_);
                        v___x_6350_ = lean_box(0);
                        v_isShared_6351_ = v_isSharedCheck_6394_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_p_6352_ = lean_ctor_get(v_c_6329_, 0);
                v_a_6353_ = lean_array_uget_borrowed(v_as_6331_, v_i_6333_);
                v_p_6354_ = lean_ctor_get(v_a_6353_, 0);
                v___x_6355_ = lean_box(0);
                lean_inc(v_x_6330_);
                lean_inc_ref(v_p_6354_);
                v___f_6356_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                lean_closure_set(v___f_6356_, 0, v_p_6354_);
                lean_closure_set(v___f_6356_, 1, v_x_6330_);
                v___x_6392_ = l_Int_Linear_instBEqPoly_beq(v_p_6352_, v_p_6354_);
                if v___x_6392_ == 0 {
                    v___x_6393_ = l_Int_Linear_Poly_isNegEq(v_p_6352_, v_p_6354_);
                    v___y_6358_ = v___x_6393_;
                    state = 2;
                    continue;
                } else {
                    v___y_6358_ = v___x_6392_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_6358_ == 0 {
                    lean_dec_ref(v___f_6356_);
                    lean_del_object(v___x_6350_);
                    lean_dec(v_snd_6348_);
                    v___x_6359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1;
                    v___x_6360_ = 1usize;
                    v___x_6361_ = lean_usize_add(v_i_6333_, v___x_6360_);
                    v___x_6362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_6329_, v_x_6330_, v_as_6331_, v_sz_6332_, v___x_6361_, v___x_6359_, v___y_6335_);
                    return v___x_6362_;
                } else {
                    lean_dec(v_x_6330_);
                    v___x_6363_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                    v___x_6364_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_6363_, v___f_6356_, v___y_6335_);
                    if lean_obj_tag(v___x_6364_) == 0 {
                        v_isSharedCheck_6382_ = (!lean_is_exclusive(v___x_6364_)) as u8;
                        if v_isSharedCheck_6382_ == 0 {
                            v_unused_6383_ = lean_ctor_get(v___x_6364_, 0);
                            lean_dec(v_unused_6383_);
                            v___x_6366_ = v___x_6364_;
                            v_isShared_6367_ = v_isSharedCheck_6382_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_6364_);
                            v___x_6366_ = lean_box(0);
                            v_isShared_6367_ = v_isSharedCheck_6382_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_6350_);
                        lean_dec(v_snd_6348_);
                        lean_dec_ref(v_c_6329_);
                        v_a_6384_ = lean_ctor_get(v___x_6364_, 0);
                        v_isSharedCheck_6391_ = (!lean_is_exclusive(v___x_6364_)) as u8;
                        if v_isSharedCheck_6391_ == 0 {
                            v___x_6386_ = v___x_6364_;
                            v_isShared_6387_ = v_isSharedCheck_6391_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6384_);
                            lean_dec(v___x_6364_);
                            v___x_6386_ = lean_box(0);
                            v_isShared_6387_ = v_isSharedCheck_6391_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_6368_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
                lean_inc_ref(v_p_6352_);
                v___x_6369_ = l_Int_Linear_Poly_addConst(v_p_6352_, v___x_6368_);
                lean_inc(v_a_6353_);
                v___x_6370_ = lean_alloc_ctor(11, 2, (0) as u32);
                lean_ctor_set(v___x_6370_, 0, v_c_6329_);
                lean_ctor_set(v___x_6370_, 1, v_a_6353_);
                v___x_6371_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6371_, 0, v___x_6369_);
                lean_ctor_set(v___x_6371_, 1, v___x_6370_);
                v___x_6372_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6372_, 0, v___x_6371_);
                v___x_6373_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6373_, 0, v___x_6372_);
                if v_isShared_6351_ == 0 {
                    lean_ctor_set(v___x_6350_, 1, v___x_6355_);
                    lean_ctor_set(v___x_6350_, 0, v___x_6373_);
                    v___x_6375_ = v___x_6350_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6381_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6381_, 0, v___x_6373_);
                    lean_ctor_set(v_reuseFailAlloc_6381_, 1, v___x_6355_);
                    v___x_6375_ = v_reuseFailAlloc_6381_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6376_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6376_, 0, v___x_6375_);
                v___x_6377_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6377_, 0, v___x_6376_);
                lean_ctor_set(v___x_6377_, 1, v_snd_6348_);
                if v_isShared_6367_ == 0 {
                    lean_ctor_set(v___x_6366_, 0, v___x_6377_);
                    v___x_6379_ = v___x_6366_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6380_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6380_, 0, v___x_6377_);
                    v___x_6379_ = v_reuseFailAlloc_6380_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6379_;
            }
            6 => {
                if v_isShared_6387_ == 0 {
                    v___x_6389_ = v___x_6386_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6390_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6390_, 0, v_a_6384_);
                    v___x_6389_ = v_reuseFailAlloc_6390_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6389_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_6396_: *mut LeanObject = *_args.add(0);
    let mut v_x_6397_: *mut LeanObject = *_args.add(1);
    let mut v_as_6398_: *mut LeanObject = *_args.add(2);
    let mut v_sz_6399_: *mut LeanObject = *_args.add(3);
    let mut v_i_6400_: *mut LeanObject = *_args.add(4);
    let mut v_b_6401_: *mut LeanObject = *_args.add(5);
    let mut v___y_6402_: *mut LeanObject = *_args.add(6);
    let mut v___y_6403_: *mut LeanObject = *_args.add(7);
    let mut v___y_6404_: *mut LeanObject = *_args.add(8);
    let mut v___y_6405_: *mut LeanObject = *_args.add(9);
    let mut v___y_6406_: *mut LeanObject = *_args.add(10);
    let mut v___y_6407_: *mut LeanObject = *_args.add(11);
    let mut v___y_6408_: *mut LeanObject = *_args.add(12);
    let mut v___y_6409_: *mut LeanObject = *_args.add(13);
    let mut v___y_6410_: *mut LeanObject = *_args.add(14);
    let mut v___y_6411_: *mut LeanObject = *_args.add(15);
    let mut v___y_6412_: *mut LeanObject = *_args.add(16);
    let mut v_sz_boxed_6413_: usize = 0;
    let mut v_i_boxed_6414_: usize = 0;
    let mut v_res_6415_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6413_ = lean_unbox_usize(v_sz_6399_);
    lean_dec(v_sz_6399_);
    v_i_boxed_6414_ = lean_unbox_usize(v_i_6400_);
    lean_dec(v_i_6400_);
    v_res_6415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_6396_, v_x_6397_, v_as_6398_, v_sz_boxed_6413_, v_i_boxed_6414_, v_b_6401_, v___y_6402_, v___y_6403_, v___y_6404_, v___y_6405_, v___y_6406_, v___y_6407_, v___y_6408_, v___y_6409_, v___y_6410_, v___y_6411_);
    lean_dec(v___y_6411_);
    lean_dec_ref(v___y_6410_);
    lean_dec(v___y_6409_);
    lean_dec_ref(v___y_6408_);
    lean_dec(v___y_6407_);
    lean_dec_ref(v___y_6406_);
    lean_dec(v___y_6405_);
    lean_dec_ref(v___y_6404_);
    lean_dec(v___y_6403_);
    lean_dec(v___y_6402_);
    lean_dec_ref(v_as_6398_);
    return v_res_6415_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(
    mut v_c_6422_: *mut LeanObject,
    mut v_x_6423_: *mut LeanObject,
    mut v_as_6424_: *mut LeanObject,
    mut v_sz_6425_: usize,
    mut v_i_6426_: usize,
    mut v_b_6427_: *mut LeanObject,
    mut v___y_6428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6430_: u8 = 0;
    let mut v___x_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6435_: u8 = 0;
    let mut v_p_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6442_: u8 = 0;
    let mut v___x_6443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6444_: usize = 0;
    let mut v___x_6445_: usize = 0;
    let mut v___x_6447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6451_: u8 = 0;
    let mut v___x_6452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6467_: u8 = 0;
    let mut v_unused_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6472_: u8 = 0;
    let mut v___x_6474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6476_: u8 = 0;
    let mut v___x_6477_: u8 = 0;
    let mut v___x_6478_: u8 = 0;
    let mut v_isSharedCheck_6479_: u8 = 0;
    let mut v_unused_6480_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6430_ = lean_usize_dec_lt(v_i_6426_, v_sz_6425_);
                if v___x_6430_ == 0 {
                    lean_dec(v_x_6423_);
                    lean_dec_ref(v_c_6422_);
                    v___x_6431_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6431_, 0, v_b_6427_);
                    return v___x_6431_;
                } else {
                    v_snd_6432_ = lean_ctor_get(v_b_6427_, 1);
                    v_isSharedCheck_6479_ = (!lean_is_exclusive(v_b_6427_)) as u8;
                    if v_isSharedCheck_6479_ == 0 {
                        v_unused_6480_ = lean_ctor_get(v_b_6427_, 0);
                        lean_dec(v_unused_6480_);
                        v___x_6434_ = v_b_6427_;
                        v_isShared_6435_ = v_isSharedCheck_6479_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6432_);
                        lean_dec(v_b_6427_);
                        v___x_6434_ = lean_box(0);
                        v_isShared_6435_ = v_isSharedCheck_6479_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_p_6436_ = lean_ctor_get(v_c_6422_, 0);
                v_a_6437_ = lean_array_uget_borrowed(v_as_6424_, v_i_6426_);
                v_p_6438_ = lean_ctor_get(v_a_6437_, 0);
                v___x_6439_ = lean_box(0);
                lean_inc(v_x_6423_);
                lean_inc_ref(v_p_6438_);
                v___f_6440_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                lean_closure_set(v___f_6440_, 0, v_p_6438_);
                lean_closure_set(v___f_6440_, 1, v_x_6423_);
                v___x_6477_ = l_Int_Linear_instBEqPoly_beq(v_p_6436_, v_p_6438_);
                if v___x_6477_ == 0 {
                    v___x_6478_ = l_Int_Linear_Poly_isNegEq(v_p_6436_, v_p_6438_);
                    v___y_6442_ = v___x_6478_;
                    state = 2;
                    continue;
                } else {
                    v___y_6442_ = v___x_6477_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_6442_ == 0 {
                    lean_dec_ref(v___f_6440_);
                    lean_del_object(v___x_6434_);
                    lean_dec(v_snd_6432_);
                    v___x_6443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1;
                    v___x_6444_ = 1usize;
                    v___x_6445_ = lean_usize_add(v_i_6426_, v___x_6444_);
                    v_i_6426_ = v___x_6445_;
                    v_b_6427_ = v___x_6443_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_x_6423_);
                    v___x_6447_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                    v___x_6448_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_6447_, v___f_6440_, v___y_6428_);
                    if lean_obj_tag(v___x_6448_) == 0 {
                        v_isSharedCheck_6467_ = (!lean_is_exclusive(v___x_6448_)) as u8;
                        if v_isSharedCheck_6467_ == 0 {
                            v_unused_6468_ = lean_ctor_get(v___x_6448_, 0);
                            lean_dec(v_unused_6468_);
                            v___x_6450_ = v___x_6448_;
                            v_isShared_6451_ = v_isSharedCheck_6467_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_6448_);
                            v___x_6450_ = lean_box(0);
                            v_isShared_6451_ = v_isSharedCheck_6467_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_6434_);
                        lean_dec(v_snd_6432_);
                        lean_dec_ref(v_c_6422_);
                        v_a_6469_ = lean_ctor_get(v___x_6448_, 0);
                        v_isSharedCheck_6476_ = (!lean_is_exclusive(v___x_6448_)) as u8;
                        if v_isSharedCheck_6476_ == 0 {
                            v___x_6471_ = v___x_6448_;
                            v_isShared_6472_ = v_isSharedCheck_6476_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6469_);
                            lean_dec(v___x_6448_);
                            v___x_6471_ = lean_box(0);
                            v_isShared_6472_ = v_isSharedCheck_6476_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_6452_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
                lean_inc_ref(v_p_6436_);
                v___x_6453_ = l_Int_Linear_Poly_addConst(v_p_6436_, v___x_6452_);
                lean_inc(v_a_6437_);
                v___x_6454_ = lean_alloc_ctor(11, 2, (0) as u32);
                lean_ctor_set(v___x_6454_, 0, v_c_6422_);
                lean_ctor_set(v___x_6454_, 1, v_a_6437_);
                v___x_6455_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6455_, 0, v___x_6453_);
                lean_ctor_set(v___x_6455_, 1, v___x_6454_);
                v___x_6456_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6456_, 0, v___x_6455_);
                v___x_6457_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6457_, 0, v___x_6456_);
                if v_isShared_6435_ == 0 {
                    lean_ctor_set(v___x_6434_, 1, v___x_6439_);
                    lean_ctor_set(v___x_6434_, 0, v___x_6457_);
                    v___x_6459_ = v___x_6434_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6466_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6466_, 0, v___x_6457_);
                    lean_ctor_set(v_reuseFailAlloc_6466_, 1, v___x_6439_);
                    v___x_6459_ = v_reuseFailAlloc_6466_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6460_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6460_, 0, v___x_6459_);
                v___x_6461_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6461_, 0, v___x_6460_);
                v___x_6462_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6462_, 0, v___x_6461_);
                lean_ctor_set(v___x_6462_, 1, v_snd_6432_);
                if v_isShared_6451_ == 0 {
                    lean_ctor_set(v___x_6450_, 0, v___x_6462_);
                    v___x_6464_ = v___x_6450_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6465_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6465_, 0, v___x_6462_);
                    v___x_6464_ = v_reuseFailAlloc_6465_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6464_;
            }
            6 => {
                if v_isShared_6472_ == 0 {
                    v___x_6474_ = v___x_6471_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6475_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6475_, 0, v_a_6469_);
                    v___x_6474_ = v_reuseFailAlloc_6475_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6474_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___boxed(
    mut v_c_6481_: *mut LeanObject,
    mut v_x_6482_: *mut LeanObject,
    mut v_as_6483_: *mut LeanObject,
    mut v_sz_6484_: *mut LeanObject,
    mut v_i_6485_: *mut LeanObject,
    mut v_b_6486_: *mut LeanObject,
    mut v___y_6487_: *mut LeanObject,
    mut v___y_6488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6489_: usize = 0;
    let mut v_i_boxed_6490_: usize = 0;
    let mut v_res_6491_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6489_ = lean_unbox_usize(v_sz_6484_);
    lean_dec(v_sz_6484_);
    v_i_boxed_6490_ = lean_unbox_usize(v_i_6485_);
    lean_dec(v_i_6485_);
    v_res_6491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_6481_, v_x_6482_, v_as_6483_, v_sz_boxed_6489_, v_i_boxed_6490_, v_b_6486_, v___y_6487_);
    lean_dec(v___y_6487_);
    lean_dec_ref(v_as_6483_);
    return v_res_6491_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(
    mut v_c_6495_: *mut LeanObject,
    mut v_x_6496_: *mut LeanObject,
    mut v_as_6497_: *mut LeanObject,
    mut v_sz_6498_: usize,
    mut v_i_6499_: usize,
    mut v_b_6500_: *mut LeanObject,
    mut v___y_6501_: *mut LeanObject,
    mut v___y_6502_: *mut LeanObject,
    mut v___y_6503_: *mut LeanObject,
    mut v___y_6504_: *mut LeanObject,
    mut v___y_6505_: *mut LeanObject,
    mut v___y_6506_: *mut LeanObject,
    mut v___y_6507_: *mut LeanObject,
    mut v___y_6508_: *mut LeanObject,
    mut v___y_6509_: *mut LeanObject,
    mut v___y_6510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6512_: u8 = 0;
    let mut v___x_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6517_: u8 = 0;
    let mut v_p_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6524_: u8 = 0;
    let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: usize = 0;
    let mut v___x_6527_: usize = 0;
    let mut v___x_6528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6533_: u8 = 0;
    let mut v___x_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6549_: u8 = 0;
    let mut v_unused_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6554_: u8 = 0;
    let mut v___x_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6558_: u8 = 0;
    let mut v___x_6559_: u8 = 0;
    let mut v___x_6560_: u8 = 0;
    let mut v_isSharedCheck_6561_: u8 = 0;
    let mut v_unused_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6512_ = lean_usize_dec_lt(v_i_6499_, v_sz_6498_);
                if v___x_6512_ == 0 {
                    lean_dec(v_x_6496_);
                    lean_dec_ref(v_c_6495_);
                    v___x_6513_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6513_, 0, v_b_6500_);
                    return v___x_6513_;
                } else {
                    v_snd_6514_ = lean_ctor_get(v_b_6500_, 1);
                    v_isSharedCheck_6561_ = (!lean_is_exclusive(v_b_6500_)) as u8;
                    if v_isSharedCheck_6561_ == 0 {
                        v_unused_6562_ = lean_ctor_get(v_b_6500_, 0);
                        lean_dec(v_unused_6562_);
                        v___x_6516_ = v_b_6500_;
                        v_isShared_6517_ = v_isSharedCheck_6561_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6514_);
                        lean_dec(v_b_6500_);
                        v___x_6516_ = lean_box(0);
                        v_isShared_6517_ = v_isSharedCheck_6561_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_p_6518_ = lean_ctor_get(v_c_6495_, 0);
                v_a_6519_ = lean_array_uget_borrowed(v_as_6497_, v_i_6499_);
                v_p_6520_ = lean_ctor_get(v_a_6519_, 0);
                v___x_6521_ = lean_box(0);
                lean_inc(v_x_6496_);
                lean_inc_ref(v_p_6520_);
                v___f_6522_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                lean_closure_set(v___f_6522_, 0, v_p_6520_);
                lean_closure_set(v___f_6522_, 1, v_x_6496_);
                v___x_6559_ = l_Int_Linear_instBEqPoly_beq(v_p_6518_, v_p_6520_);
                if v___x_6559_ == 0 {
                    v___x_6560_ = l_Int_Linear_Poly_isNegEq(v_p_6518_, v_p_6520_);
                    v___y_6524_ = v___x_6560_;
                    state = 2;
                    continue;
                } else {
                    v___y_6524_ = v___x_6559_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_6524_ == 0 {
                    lean_dec_ref(v___f_6522_);
                    lean_del_object(v___x_6516_);
                    lean_dec(v_snd_6514_);
                    v___x_6525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0;
                    v___x_6526_ = 1usize;
                    v___x_6527_ = lean_usize_add(v_i_6499_, v___x_6526_);
                    v___x_6528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_6495_, v_x_6496_, v_as_6497_, v_sz_6498_, v___x_6527_, v___x_6525_, v___y_6501_);
                    return v___x_6528_;
                } else {
                    lean_dec(v_x_6496_);
                    v___x_6529_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                    v___x_6530_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_6529_, v___f_6522_, v___y_6501_);
                    if lean_obj_tag(v___x_6530_) == 0 {
                        v_isSharedCheck_6549_ = (!lean_is_exclusive(v___x_6530_)) as u8;
                        if v_isSharedCheck_6549_ == 0 {
                            v_unused_6550_ = lean_ctor_get(v___x_6530_, 0);
                            lean_dec(v_unused_6550_);
                            v___x_6532_ = v___x_6530_;
                            v_isShared_6533_ = v_isSharedCheck_6549_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_6530_);
                            v___x_6532_ = lean_box(0);
                            v_isShared_6533_ = v_isSharedCheck_6549_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_6516_);
                        lean_dec(v_snd_6514_);
                        lean_dec_ref(v_c_6495_);
                        v_a_6551_ = lean_ctor_get(v___x_6530_, 0);
                        v_isSharedCheck_6558_ = (!lean_is_exclusive(v___x_6530_)) as u8;
                        if v_isSharedCheck_6558_ == 0 {
                            v___x_6553_ = v___x_6530_;
                            v_isShared_6554_ = v_isSharedCheck_6558_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6551_);
                            lean_dec(v___x_6530_);
                            v___x_6553_ = lean_box(0);
                            v_isShared_6554_ = v_isSharedCheck_6558_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_6534_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
                lean_inc_ref(v_p_6518_);
                v___x_6535_ = l_Int_Linear_Poly_addConst(v_p_6518_, v___x_6534_);
                lean_inc(v_a_6519_);
                v___x_6536_ = lean_alloc_ctor(11, 2, (0) as u32);
                lean_ctor_set(v___x_6536_, 0, v_c_6495_);
                lean_ctor_set(v___x_6536_, 1, v_a_6519_);
                v___x_6537_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6537_, 0, v___x_6535_);
                lean_ctor_set(v___x_6537_, 1, v___x_6536_);
                v___x_6538_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6538_, 0, v___x_6537_);
                v___x_6539_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6539_, 0, v___x_6538_);
                if v_isShared_6517_ == 0 {
                    lean_ctor_set(v___x_6516_, 1, v___x_6521_);
                    lean_ctor_set(v___x_6516_, 0, v___x_6539_);
                    v___x_6541_ = v___x_6516_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6548_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6548_, 0, v___x_6539_);
                    lean_ctor_set(v_reuseFailAlloc_6548_, 1, v___x_6521_);
                    v___x_6541_ = v_reuseFailAlloc_6548_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6542_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6542_, 0, v___x_6541_);
                v___x_6543_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6543_, 0, v___x_6542_);
                v___x_6544_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6544_, 0, v___x_6543_);
                lean_ctor_set(v___x_6544_, 1, v_snd_6514_);
                if v_isShared_6533_ == 0 {
                    lean_ctor_set(v___x_6532_, 0, v___x_6544_);
                    v___x_6546_ = v___x_6532_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6547_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6547_, 0, v___x_6544_);
                    v___x_6546_ = v_reuseFailAlloc_6547_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6546_;
            }
            6 => {
                if v_isShared_6554_ == 0 {
                    v___x_6556_ = v___x_6553_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6557_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6557_, 0, v_a_6551_);
                    v___x_6556_ = v_reuseFailAlloc_6557_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6556_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_6563_: *mut LeanObject = *_args.add(0);
    let mut v_x_6564_: *mut LeanObject = *_args.add(1);
    let mut v_as_6565_: *mut LeanObject = *_args.add(2);
    let mut v_sz_6566_: *mut LeanObject = *_args.add(3);
    let mut v_i_6567_: *mut LeanObject = *_args.add(4);
    let mut v_b_6568_: *mut LeanObject = *_args.add(5);
    let mut v___y_6569_: *mut LeanObject = *_args.add(6);
    let mut v___y_6570_: *mut LeanObject = *_args.add(7);
    let mut v___y_6571_: *mut LeanObject = *_args.add(8);
    let mut v___y_6572_: *mut LeanObject = *_args.add(9);
    let mut v___y_6573_: *mut LeanObject = *_args.add(10);
    let mut v___y_6574_: *mut LeanObject = *_args.add(11);
    let mut v___y_6575_: *mut LeanObject = *_args.add(12);
    let mut v___y_6576_: *mut LeanObject = *_args.add(13);
    let mut v___y_6577_: *mut LeanObject = *_args.add(14);
    let mut v___y_6578_: *mut LeanObject = *_args.add(15);
    let mut v___y_6579_: *mut LeanObject = *_args.add(16);
    let mut v_sz_boxed_6580_: usize = 0;
    let mut v_i_boxed_6581_: usize = 0;
    let mut v_res_6582_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6580_ = lean_unbox_usize(v_sz_6566_);
    lean_dec(v_sz_6566_);
    v_i_boxed_6581_ = lean_unbox_usize(v_i_6567_);
    lean_dec(v_i_6567_);
    v_res_6582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_6563_, v_x_6564_, v_as_6565_, v_sz_boxed_6580_, v_i_boxed_6581_, v_b_6568_, v___y_6569_, v___y_6570_, v___y_6571_, v___y_6572_, v___y_6573_, v___y_6574_, v___y_6575_, v___y_6576_, v___y_6577_, v___y_6578_);
    lean_dec(v___y_6578_);
    lean_dec_ref(v___y_6577_);
    lean_dec(v___y_6576_);
    lean_dec_ref(v___y_6575_);
    lean_dec(v___y_6574_);
    lean_dec_ref(v___y_6573_);
    lean_dec(v___y_6572_);
    lean_dec_ref(v___y_6571_);
    lean_dec(v___y_6570_);
    lean_dec(v___y_6569_);
    lean_dec_ref(v_as_6565_);
    return v_res_6582_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(
    mut v_init_6583_: *mut LeanObject,
    mut v_c_6584_: *mut LeanObject,
    mut v_x_6585_: *mut LeanObject,
    mut v_n_6586_: *mut LeanObject,
    mut v_b_6587_: *mut LeanObject,
    mut v___y_6588_: *mut LeanObject,
    mut v___y_6589_: *mut LeanObject,
    mut v___y_6590_: *mut LeanObject,
    mut v___y_6591_: *mut LeanObject,
    mut v___y_6592_: *mut LeanObject,
    mut v___y_6593_: *mut LeanObject,
    mut v___y_6594_: *mut LeanObject,
    mut v___y_6595_: *mut LeanObject,
    mut v___y_6596_: *mut LeanObject,
    mut v___y_6597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_6599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6602_: usize = 0;
    let mut v___x_6603_: usize = 0;
    let mut v___x_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6608_: u8 = 0;
    let mut v_fst_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6619_: u8 = 0;
    let mut v_a_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6623_: u8 = 0;
    let mut v___x_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6627_: u8 = 0;
    let mut v_vs_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6631_: usize = 0;
    let mut v___x_6632_: usize = 0;
    let mut v___x_6633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6637_: u8 = 0;
    let mut v_fst_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6648_: u8 = 0;
    let mut v_a_6649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6652_: u8 = 0;
    let mut v___x_6654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6656_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_6586_) == 0 {
                    v_cs_6599_ = lean_ctor_get(v_n_6586_, 0);
                    v___x_6600_ = lean_box(0);
                    v___x_6601_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6601_, 0, v___x_6600_);
                    lean_ctor_set(v___x_6601_, 1, v_b_6587_);
                    v_sz_6602_ = lean_array_size(v_cs_6599_);
                    v___x_6603_ = 0usize;
                    v___x_6604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_6583_, v_c_6584_, v_x_6585_, v_cs_6599_, v_sz_6602_, v___x_6603_, v___x_6601_, v___y_6588_, v___y_6589_, v___y_6590_, v___y_6591_, v___y_6592_, v___y_6593_, v___y_6594_, v___y_6595_, v___y_6596_, v___y_6597_);
                    if lean_obj_tag(v___x_6604_) == 0 {
                        v_a_6605_ = lean_ctor_get(v___x_6604_, 0);
                        v_isSharedCheck_6619_ = (!lean_is_exclusive(v___x_6604_)) as u8;
                        if v_isSharedCheck_6619_ == 0 {
                            v___x_6607_ = v___x_6604_;
                            v_isShared_6608_ = v_isSharedCheck_6619_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6605_);
                            lean_dec(v___x_6604_);
                            v___x_6607_ = lean_box(0);
                            v_isShared_6608_ = v_isSharedCheck_6619_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6620_ = lean_ctor_get(v___x_6604_, 0);
                        v_isSharedCheck_6627_ = (!lean_is_exclusive(v___x_6604_)) as u8;
                        if v_isSharedCheck_6627_ == 0 {
                            v___x_6622_ = v___x_6604_;
                            v_isShared_6623_ = v_isSharedCheck_6627_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_6620_);
                            lean_dec(v___x_6604_);
                            v___x_6622_ = lean_box(0);
                            v_isShared_6623_ = v_isSharedCheck_6627_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_6628_ = lean_ctor_get(v_n_6586_, 0);
                    v___x_6629_ = lean_box(0);
                    v___x_6630_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6630_, 0, v___x_6629_);
                    lean_ctor_set(v___x_6630_, 1, v_b_6587_);
                    v_sz_6631_ = lean_array_size(v_vs_6628_);
                    v___x_6632_ = 0usize;
                    v___x_6633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_6584_, v_x_6585_, v_vs_6628_, v_sz_6631_, v___x_6632_, v___x_6630_, v___y_6588_, v___y_6589_, v___y_6590_, v___y_6591_, v___y_6592_, v___y_6593_, v___y_6594_, v___y_6595_, v___y_6596_, v___y_6597_);
                    if lean_obj_tag(v___x_6633_) == 0 {
                        v_a_6634_ = lean_ctor_get(v___x_6633_, 0);
                        v_isSharedCheck_6648_ = (!lean_is_exclusive(v___x_6633_)) as u8;
                        if v_isSharedCheck_6648_ == 0 {
                            v___x_6636_ = v___x_6633_;
                            v_isShared_6637_ = v_isSharedCheck_6648_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6634_);
                            lean_dec(v___x_6633_);
                            v___x_6636_ = lean_box(0);
                            v_isShared_6637_ = v_isSharedCheck_6648_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_6649_ = lean_ctor_get(v___x_6633_, 0);
                        v_isSharedCheck_6656_ = (!lean_is_exclusive(v___x_6633_)) as u8;
                        if v_isSharedCheck_6656_ == 0 {
                            v___x_6651_ = v___x_6633_;
                            v_isShared_6652_ = v_isSharedCheck_6656_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_6649_);
                            lean_dec(v___x_6633_);
                            v___x_6651_ = lean_box(0);
                            v_isShared_6652_ = v_isSharedCheck_6656_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_6609_ = lean_ctor_get(v_a_6605_, 0);
                if lean_obj_tag(v_fst_6609_) == 0 {
                    v_snd_6610_ = lean_ctor_get(v_a_6605_, 1);
                    lean_inc(v_snd_6610_);
                    lean_dec(v_a_6605_);
                    v___x_6611_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6611_, 0, v_snd_6610_);
                    if v_isShared_6608_ == 0 {
                        lean_ctor_set(v___x_6607_, 0, v___x_6611_);
                        v___x_6613_ = v___x_6607_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6614_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6614_, 0, v___x_6611_);
                        v___x_6613_ = v_reuseFailAlloc_6614_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_6609_);
                    lean_dec(v_a_6605_);
                    v_val_6615_ = lean_ctor_get(v_fst_6609_, 0);
                    lean_inc(v_val_6615_);
                    lean_dec_ref_known(v_fst_6609_, 1);
                    if v_isShared_6608_ == 0 {
                        lean_ctor_set(v___x_6607_, 0, v_val_6615_);
                        v___x_6617_ = v___x_6607_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6618_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6618_, 0, v_val_6615_);
                        v___x_6617_ = v_reuseFailAlloc_6618_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6613_;
            }
            3 => {
                return v___x_6617_;
            }
            4 => {
                if v_isShared_6623_ == 0 {
                    v___x_6625_ = v___x_6622_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6626_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6626_, 0, v_a_6620_);
                    v___x_6625_ = v_reuseFailAlloc_6626_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6625_;
            }
            6 => {
                v_fst_6638_ = lean_ctor_get(v_a_6634_, 0);
                if lean_obj_tag(v_fst_6638_) == 0 {
                    v_snd_6639_ = lean_ctor_get(v_a_6634_, 1);
                    lean_inc(v_snd_6639_);
                    lean_dec(v_a_6634_);
                    v___x_6640_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6640_, 0, v_snd_6639_);
                    if v_isShared_6637_ == 0 {
                        lean_ctor_set(v___x_6636_, 0, v___x_6640_);
                        v___x_6642_ = v___x_6636_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6643_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6643_, 0, v___x_6640_);
                        v___x_6642_ = v_reuseFailAlloc_6643_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_6638_);
                    lean_dec(v_a_6634_);
                    v_val_6644_ = lean_ctor_get(v_fst_6638_, 0);
                    lean_inc(v_val_6644_);
                    lean_dec_ref_known(v_fst_6638_, 1);
                    if v_isShared_6637_ == 0 {
                        lean_ctor_set(v___x_6636_, 0, v_val_6644_);
                        v___x_6646_ = v___x_6636_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6647_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6647_, 0, v_val_6644_);
                        v___x_6646_ = v_reuseFailAlloc_6647_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_6642_;
            }
            8 => {
                return v___x_6646_;
            }
            9 => {
                if v_isShared_6652_ == 0 {
                    v___x_6654_ = v___x_6651_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6655_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6655_, 0, v_a_6649_);
                    v___x_6654_ = v_reuseFailAlloc_6655_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6654_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(
    mut v_init_6657_: *mut LeanObject,
    mut v_c_6658_: *mut LeanObject,
    mut v_x_6659_: *mut LeanObject,
    mut v_as_6660_: *mut LeanObject,
    mut v_sz_6661_: usize,
    mut v_i_6662_: usize,
    mut v_b_6663_: *mut LeanObject,
    mut v___y_6664_: *mut LeanObject,
    mut v___y_6665_: *mut LeanObject,
    mut v___y_6666_: *mut LeanObject,
    mut v___y_6667_: *mut LeanObject,
    mut v___y_6668_: *mut LeanObject,
    mut v___y_6669_: *mut LeanObject,
    mut v___y_6670_: *mut LeanObject,
    mut v___y_6671_: *mut LeanObject,
    mut v___y_6672_: *mut LeanObject,
    mut v___y_6673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6675_: u8 = 0;
    let mut v___x_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6680_: u8 = 0;
    let mut v_a_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6686_: u8 = 0;
    let mut v___x_6687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: usize = 0;
    let mut v___x_6699_: usize = 0;
    let mut v_reuseFailAlloc_6701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6702_: u8 = 0;
    let mut v_a_6703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6706_: u8 = 0;
    let mut v___x_6708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6710_: u8 = 0;
    let mut v_isSharedCheck_6711_: u8 = 0;
    let mut v_unused_6712_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6675_ = lean_usize_dec_lt(v_i_6662_, v_sz_6661_);
                if v___x_6675_ == 0 {
                    lean_dec(v_x_6659_);
                    lean_dec_ref(v_c_6658_);
                    v___x_6676_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6676_, 0, v_b_6663_);
                    return v___x_6676_;
                } else {
                    v_snd_6677_ = lean_ctor_get(v_b_6663_, 1);
                    v_isSharedCheck_6711_ = (!lean_is_exclusive(v_b_6663_)) as u8;
                    if v_isSharedCheck_6711_ == 0 {
                        v_unused_6712_ = lean_ctor_get(v_b_6663_, 0);
                        lean_dec(v_unused_6712_);
                        v___x_6679_ = v_b_6663_;
                        v_isShared_6680_ = v_isSharedCheck_6711_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6677_);
                        lean_dec(v_b_6663_);
                        v___x_6679_ = lean_box(0);
                        v_isShared_6680_ = v_isSharedCheck_6711_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6681_ = lean_array_uget_borrowed(v_as_6660_, v_i_6662_);
                lean_inc(v_snd_6677_);
                lean_inc(v_x_6659_);
                lean_inc_ref(v_c_6658_);
                v___x_6682_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_6657_, v_c_6658_, v_x_6659_, v_a_6681_, v_snd_6677_, v___y_6664_, v___y_6665_, v___y_6666_, v___y_6667_, v___y_6668_, v___y_6669_, v___y_6670_, v___y_6671_, v___y_6672_, v___y_6673_);
                if lean_obj_tag(v___x_6682_) == 0 {
                    v_a_6683_ = lean_ctor_get(v___x_6682_, 0);
                    v_isSharedCheck_6702_ = (!lean_is_exclusive(v___x_6682_)) as u8;
                    if v_isSharedCheck_6702_ == 0 {
                        v___x_6685_ = v___x_6682_;
                        v_isShared_6686_ = v_isSharedCheck_6702_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6683_);
                        lean_dec(v___x_6682_);
                        v___x_6685_ = lean_box(0);
                        v_isShared_6686_ = v_isSharedCheck_6702_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6679_);
                    lean_dec(v_snd_6677_);
                    lean_dec(v_x_6659_);
                    lean_dec_ref(v_c_6658_);
                    v_a_6703_ = lean_ctor_get(v___x_6682_, 0);
                    v_isSharedCheck_6710_ = (!lean_is_exclusive(v___x_6682_)) as u8;
                    if v_isSharedCheck_6710_ == 0 {
                        v___x_6705_ = v___x_6682_;
                        v_isShared_6706_ = v_isSharedCheck_6710_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_6703_);
                        lean_dec(v___x_6682_);
                        v___x_6705_ = lean_box(0);
                        v_isShared_6706_ = v_isSharedCheck_6710_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_6683_) == 0 {
                    lean_dec(v_x_6659_);
                    lean_dec_ref(v_c_6658_);
                    v___x_6687_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6687_, 0, v_a_6683_);
                    if v_isShared_6680_ == 0 {
                        lean_ctor_set(v___x_6679_, 0, v___x_6687_);
                        v___x_6689_ = v___x_6679_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6693_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6693_, 0, v___x_6687_);
                        lean_ctor_set(v_reuseFailAlloc_6693_, 1, v_snd_6677_);
                        v___x_6689_ = v_reuseFailAlloc_6693_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6685_);
                    lean_dec(v_snd_6677_);
                    v_a_6694_ = lean_ctor_get(v_a_6683_, 0);
                    lean_inc(v_a_6694_);
                    lean_dec_ref_known(v_a_6683_, 1);
                    v___x_6695_ = lean_box(0);
                    if v_isShared_6680_ == 0 {
                        lean_ctor_set(v___x_6679_, 1, v_a_6694_);
                        lean_ctor_set(v___x_6679_, 0, v___x_6695_);
                        v___x_6697_ = v___x_6679_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6701_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6701_, 0, v___x_6695_);
                        lean_ctor_set(v_reuseFailAlloc_6701_, 1, v_a_6694_);
                        v___x_6697_ = v_reuseFailAlloc_6701_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6686_ == 0 {
                    lean_ctor_set(v___x_6685_, 0, v___x_6689_);
                    v___x_6691_ = v___x_6685_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6692_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6692_, 0, v___x_6689_);
                    v___x_6691_ = v_reuseFailAlloc_6692_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6691_;
            }
            5 => {
                v___x_6698_ = 1usize;
                v___x_6699_ = lean_usize_add(v_i_6662_, v___x_6698_);
                v_i_6662_ = v___x_6699_;
                v_b_6663_ = v___x_6697_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_6706_ == 0 {
                    v___x_6708_ = v___x_6705_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6709_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6709_, 0, v_a_6703_);
                    v___x_6708_ = v_reuseFailAlloc_6709_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_init_6713_: *mut LeanObject = *_args.add(0);
    let mut v_c_6714_: *mut LeanObject = *_args.add(1);
    let mut v_x_6715_: *mut LeanObject = *_args.add(2);
    let mut v_as_6716_: *mut LeanObject = *_args.add(3);
    let mut v_sz_6717_: *mut LeanObject = *_args.add(4);
    let mut v_i_6718_: *mut LeanObject = *_args.add(5);
    let mut v_b_6719_: *mut LeanObject = *_args.add(6);
    let mut v___y_6720_: *mut LeanObject = *_args.add(7);
    let mut v___y_6721_: *mut LeanObject = *_args.add(8);
    let mut v___y_6722_: *mut LeanObject = *_args.add(9);
    let mut v___y_6723_: *mut LeanObject = *_args.add(10);
    let mut v___y_6724_: *mut LeanObject = *_args.add(11);
    let mut v___y_6725_: *mut LeanObject = *_args.add(12);
    let mut v___y_6726_: *mut LeanObject = *_args.add(13);
    let mut v___y_6727_: *mut LeanObject = *_args.add(14);
    let mut v___y_6728_: *mut LeanObject = *_args.add(15);
    let mut v___y_6729_: *mut LeanObject = *_args.add(16);
    let mut v___y_6730_: *mut LeanObject = *_args.add(17);
    let mut v_sz_boxed_6731_: usize = 0;
    let mut v_i_boxed_6732_: usize = 0;
    let mut v_res_6733_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6731_ = lean_unbox_usize(v_sz_6717_);
    lean_dec(v_sz_6717_);
    v_i_boxed_6732_ = lean_unbox_usize(v_i_6718_);
    lean_dec(v_i_6718_);
    v_res_6733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_6713_, v_c_6714_, v_x_6715_, v_as_6716_, v_sz_boxed_6731_, v_i_boxed_6732_, v_b_6719_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_, v___y_6724_, v___y_6725_, v___y_6726_, v___y_6727_, v___y_6728_, v___y_6729_);
    lean_dec(v___y_6729_);
    lean_dec_ref(v___y_6728_);
    lean_dec(v___y_6727_);
    lean_dec_ref(v___y_6726_);
    lean_dec(v___y_6725_);
    lean_dec_ref(v___y_6724_);
    lean_dec(v___y_6723_);
    lean_dec_ref(v___y_6722_);
    lean_dec(v___y_6721_);
    lean_dec(v___y_6720_);
    lean_dec_ref(v_as_6716_);
    lean_dec_ref(v_init_6713_);
    return v_res_6733_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6___boxed(
    mut v_init_6734_: *mut LeanObject,
    mut v_c_6735_: *mut LeanObject,
    mut v_x_6736_: *mut LeanObject,
    mut v_n_6737_: *mut LeanObject,
    mut v_b_6738_: *mut LeanObject,
    mut v___y_6739_: *mut LeanObject,
    mut v___y_6740_: *mut LeanObject,
    mut v___y_6741_: *mut LeanObject,
    mut v___y_6742_: *mut LeanObject,
    mut v___y_6743_: *mut LeanObject,
    mut v___y_6744_: *mut LeanObject,
    mut v___y_6745_: *mut LeanObject,
    mut v___y_6746_: *mut LeanObject,
    mut v___y_6747_: *mut LeanObject,
    mut v___y_6748_: *mut LeanObject,
    mut v___y_6749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6750_: *mut LeanObject = core::ptr::null_mut();
    v_res_6750_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_6734_, v_c_6735_, v_x_6736_, v_n_6737_, v_b_6738_, v___y_6739_, v___y_6740_, v___y_6741_, v___y_6742_, v___y_6743_, v___y_6744_, v___y_6745_, v___y_6746_, v___y_6747_, v___y_6748_);
    lean_dec(v___y_6748_);
    lean_dec_ref(v___y_6747_);
    lean_dec(v___y_6746_);
    lean_dec_ref(v___y_6745_);
    lean_dec(v___y_6744_);
    lean_dec_ref(v___y_6743_);
    lean_dec(v___y_6742_);
    lean_dec_ref(v___y_6741_);
    lean_dec(v___y_6740_);
    lean_dec(v___y_6739_);
    lean_dec_ref(v_n_6737_);
    lean_dec_ref(v_init_6734_);
    return v_res_6750_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(
    mut v_c_6751_: *mut LeanObject,
    mut v_x_6752_: *mut LeanObject,
    mut v_t_6753_: *mut LeanObject,
    mut v_init_6754_: *mut LeanObject,
    mut v___y_6755_: *mut LeanObject,
    mut v___y_6756_: *mut LeanObject,
    mut v___y_6757_: *mut LeanObject,
    mut v___y_6758_: *mut LeanObject,
    mut v___y_6759_: *mut LeanObject,
    mut v___y_6760_: *mut LeanObject,
    mut v___y_6761_: *mut LeanObject,
    mut v___y_6762_: *mut LeanObject,
    mut v___y_6763_: *mut LeanObject,
    mut v___y_6764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_6766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6772_: u8 = 0;
    let mut v_a_6773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6780_: usize = 0;
    let mut v___x_6781_: usize = 0;
    let mut v___x_6782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6786_: u8 = 0;
    let mut v_fst_6787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6796_: u8 = 0;
    let mut v_a_6797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6800_: u8 = 0;
    let mut v___x_6802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6804_: u8 = 0;
    let mut v_isSharedCheck_6805_: u8 = 0;
    let mut v_a_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6809_: u8 = 0;
    let mut v___x_6811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6813_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_6766_ = lean_ctor_get(v_t_6753_, 0);
                v_tail_6767_ = lean_ctor_get(v_t_6753_, 1);
                lean_inc(v_x_6752_);
                lean_inc_ref(v_c_6751_);
                lean_inc_ref(v_init_6754_);
                v___x_6768_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_6754_, v_c_6751_, v_x_6752_, v_root_6766_, v_init_6754_, v___y_6755_, v___y_6756_, v___y_6757_, v___y_6758_, v___y_6759_, v___y_6760_, v___y_6761_, v___y_6762_, v___y_6763_, v___y_6764_);
                lean_dec_ref(v_init_6754_);
                if lean_obj_tag(v___x_6768_) == 0 {
                    v_a_6769_ = lean_ctor_get(v___x_6768_, 0);
                    v_isSharedCheck_6805_ = (!lean_is_exclusive(v___x_6768_)) as u8;
                    if v_isSharedCheck_6805_ == 0 {
                        v___x_6771_ = v___x_6768_;
                        v_isShared_6772_ = v_isSharedCheck_6805_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6769_);
                        lean_dec(v___x_6768_);
                        v___x_6771_ = lean_box(0);
                        v_isShared_6772_ = v_isSharedCheck_6805_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_x_6752_);
                    lean_dec_ref(v_c_6751_);
                    v_a_6806_ = lean_ctor_get(v___x_6768_, 0);
                    v_isSharedCheck_6813_ = (!lean_is_exclusive(v___x_6768_)) as u8;
                    if v_isSharedCheck_6813_ == 0 {
                        v___x_6808_ = v___x_6768_;
                        v_isShared_6809_ = v_isSharedCheck_6813_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_6806_);
                        lean_dec(v___x_6768_);
                        v___x_6808_ = lean_box(0);
                        v_isShared_6809_ = v_isSharedCheck_6813_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_6769_) == 0 {
                    lean_dec(v_x_6752_);
                    lean_dec_ref(v_c_6751_);
                    v_a_6773_ = lean_ctor_get(v_a_6769_, 0);
                    lean_inc(v_a_6773_);
                    lean_dec_ref_known(v_a_6769_, 1);
                    if v_isShared_6772_ == 0 {
                        lean_ctor_set(v___x_6771_, 0, v_a_6773_);
                        v___x_6775_ = v___x_6771_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6776_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6776_, 0, v_a_6773_);
                        v___x_6775_ = v_reuseFailAlloc_6776_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6771_);
                    v_a_6777_ = lean_ctor_get(v_a_6769_, 0);
                    lean_inc(v_a_6777_);
                    lean_dec_ref_known(v_a_6769_, 1);
                    v___x_6778_ = lean_box(0);
                    v___x_6779_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6779_, 0, v___x_6778_);
                    lean_ctor_set(v___x_6779_, 1, v_a_6777_);
                    v_sz_6780_ = lean_array_size(v_tail_6767_);
                    v___x_6781_ = 0usize;
                    v___x_6782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_6751_, v_x_6752_, v_tail_6767_, v_sz_6780_, v___x_6781_, v___x_6779_, v___y_6755_, v___y_6756_, v___y_6757_, v___y_6758_, v___y_6759_, v___y_6760_, v___y_6761_, v___y_6762_, v___y_6763_, v___y_6764_);
                    if lean_obj_tag(v___x_6782_) == 0 {
                        v_a_6783_ = lean_ctor_get(v___x_6782_, 0);
                        v_isSharedCheck_6796_ = (!lean_is_exclusive(v___x_6782_)) as u8;
                        if v_isSharedCheck_6796_ == 0 {
                            v___x_6785_ = v___x_6782_;
                            v_isShared_6786_ = v_isSharedCheck_6796_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6783_);
                            lean_dec(v___x_6782_);
                            v___x_6785_ = lean_box(0);
                            v_isShared_6786_ = v_isSharedCheck_6796_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_6797_ = lean_ctor_get(v___x_6782_, 0);
                        v_isSharedCheck_6804_ = (!lean_is_exclusive(v___x_6782_)) as u8;
                        if v_isSharedCheck_6804_ == 0 {
                            v___x_6799_ = v___x_6782_;
                            v_isShared_6800_ = v_isSharedCheck_6804_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6797_);
                            lean_dec(v___x_6782_);
                            v___x_6799_ = lean_box(0);
                            v_isShared_6800_ = v_isSharedCheck_6804_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_6775_;
            }
            3 => {
                v_fst_6787_ = lean_ctor_get(v_a_6783_, 0);
                if lean_obj_tag(v_fst_6787_) == 0 {
                    v_snd_6788_ = lean_ctor_get(v_a_6783_, 1);
                    lean_inc(v_snd_6788_);
                    lean_dec(v_a_6783_);
                    if v_isShared_6786_ == 0 {
                        lean_ctor_set(v___x_6785_, 0, v_snd_6788_);
                        v___x_6790_ = v___x_6785_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6791_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6791_, 0, v_snd_6788_);
                        v___x_6790_ = v_reuseFailAlloc_6791_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_6787_);
                    lean_dec(v_a_6783_);
                    v_val_6792_ = lean_ctor_get(v_fst_6787_, 0);
                    lean_inc(v_val_6792_);
                    lean_dec_ref_known(v_fst_6787_, 1);
                    if v_isShared_6786_ == 0 {
                        lean_ctor_set(v___x_6785_, 0, v_val_6792_);
                        v___x_6794_ = v___x_6785_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6795_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6795_, 0, v_val_6792_);
                        v___x_6794_ = v_reuseFailAlloc_6795_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_6790_;
            }
            5 => {
                return v___x_6794_;
            }
            6 => {
                if v_isShared_6800_ == 0 {
                    v___x_6802_ = v___x_6799_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6803_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6803_, 0, v_a_6797_);
                    v___x_6802_ = v_reuseFailAlloc_6803_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6802_;
            }
            8 => {
                if v_isShared_6809_ == 0 {
                    v___x_6811_ = v___x_6808_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6812_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6812_, 0, v_a_6806_);
                    v___x_6811_ = v_reuseFailAlloc_6812_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6811_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2___boxed(
    mut v_c_6814_: *mut LeanObject,
    mut v_x_6815_: *mut LeanObject,
    mut v_t_6816_: *mut LeanObject,
    mut v_init_6817_: *mut LeanObject,
    mut v___y_6818_: *mut LeanObject,
    mut v___y_6819_: *mut LeanObject,
    mut v___y_6820_: *mut LeanObject,
    mut v___y_6821_: *mut LeanObject,
    mut v___y_6822_: *mut LeanObject,
    mut v___y_6823_: *mut LeanObject,
    mut v___y_6824_: *mut LeanObject,
    mut v___y_6825_: *mut LeanObject,
    mut v___y_6826_: *mut LeanObject,
    mut v___y_6827_: *mut LeanObject,
    mut v___y_6828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6829_: *mut LeanObject = core::ptr::null_mut();
    v_res_6829_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_6814_, v_x_6815_, v_t_6816_, v_init_6817_, v___y_6818_, v___y_6819_, v___y_6820_, v___y_6821_, v___y_6822_, v___y_6823_, v___y_6824_, v___y_6825_, v___y_6826_, v___y_6827_);
    lean_dec(v___y_6827_);
    lean_dec_ref(v___y_6826_);
    lean_dec(v___y_6825_);
    lean_dec_ref(v___y_6824_);
    lean_dec(v___y_6823_);
    lean_dec_ref(v___y_6822_);
    lean_dec(v___y_6821_);
    lean_dec_ref(v___y_6820_);
    lean_dec(v___y_6819_);
    lean_dec(v___y_6818_);
    lean_dec_ref(v_t_6816_);
    return v_res_6829_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(
    mut v_x_6830_: *mut LeanObject,
    mut v_c_6831_: *mut LeanObject,
    mut v_a_6832_: *mut LeanObject,
    mut v_a_6833_: *mut LeanObject,
    mut v_a_6834_: *mut LeanObject,
    mut v_a_6835_: *mut LeanObject,
    mut v_a_6836_: *mut LeanObject,
    mut v_a_6837_: *mut LeanObject,
    mut v_a_6838_: *mut LeanObject,
    mut v_a_6839_: *mut LeanObject,
    mut v_a_6840_: *mut LeanObject,
    mut v_a_6841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6853_: u8 = 0;
    let mut v_fst_6854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6862_: u8 = 0;
    let mut v_a_6863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6866_: u8 = 0;
    let mut v___x_6868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6870_: u8 = 0;
    let mut v_diseqs_6871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6874_: u8 = 0;
    let mut v___x_6875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6880_: u8 = 0;
    let mut v___x_6882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6843_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_6832_, v_a_6840_);
                if lean_obj_tag(v___x_6843_) == 0 {
                    v_a_6844_ = lean_ctor_get(v___x_6843_, 0);
                    lean_inc(v_a_6844_);
                    lean_dec_ref_known(v___x_6843_, 1);
                    v_diseqs_6871_ = lean_ctor_get(v_a_6844_, 9);
                    lean_inc_ref(v_diseqs_6871_);
                    lean_dec(v_a_6844_);
                    v_size_6872_ = lean_ctor_get(v_diseqs_6871_, 2);
                    v___x_6873_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
                    v___x_6874_ = lean_nat_dec_lt(v_x_6830_, v_size_6872_);
                    if v___x_6874_ == 0 {
                        lean_dec_ref(v_diseqs_6871_);
                        v___x_6875_ = l_outOfBounds___redArg(v___x_6873_);
                        v___y_6846_ = v___x_6875_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6876_ = l_Lean_PersistentArray_get_x21___redArg(
                            v___x_6873_,
                            v_diseqs_6871_,
                            v_x_6830_,
                        );
                        lean_dec_ref(v_diseqs_6871_);
                        v___y_6846_ = v___x_6876_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_c_6831_);
                    lean_dec(v_x_6830_);
                    v_a_6877_ = lean_ctor_get(v___x_6843_, 0);
                    v_isSharedCheck_6884_ = (!lean_is_exclusive(v___x_6843_)) as u8;
                    if v_isSharedCheck_6884_ == 0 {
                        v___x_6879_ = v___x_6843_;
                        v_isShared_6880_ = v_isSharedCheck_6884_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_6877_);
                        lean_dec(v___x_6843_);
                        v___x_6879_ = lean_box(0);
                        v_isShared_6880_ = v_isSharedCheck_6884_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6847_ = lean_box(0);
                v___x_6848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0;
                v___x_6849_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_6831_, v_x_6830_, v___y_6846_, v___x_6848_, v_a_6832_, v_a_6833_, v_a_6834_, v_a_6835_, v_a_6836_, v_a_6837_, v_a_6838_, v_a_6839_, v_a_6840_, v_a_6841_);
                lean_dec_ref(v___y_6846_);
                if lean_obj_tag(v___x_6849_) == 0 {
                    v_a_6850_ = lean_ctor_get(v___x_6849_, 0);
                    v_isSharedCheck_6862_ = (!lean_is_exclusive(v___x_6849_)) as u8;
                    if v_isSharedCheck_6862_ == 0 {
                        v___x_6852_ = v___x_6849_;
                        v_isShared_6853_ = v_isSharedCheck_6862_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6850_);
                        lean_dec(v___x_6849_);
                        v___x_6852_ = lean_box(0);
                        v_isShared_6853_ = v_isSharedCheck_6862_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_6863_ = lean_ctor_get(v___x_6849_, 0);
                    v_isSharedCheck_6870_ = (!lean_is_exclusive(v___x_6849_)) as u8;
                    if v_isSharedCheck_6870_ == 0 {
                        v___x_6865_ = v___x_6849_;
                        v_isShared_6866_ = v_isSharedCheck_6870_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6863_);
                        lean_dec(v___x_6849_);
                        v___x_6865_ = lean_box(0);
                        v_isShared_6866_ = v_isSharedCheck_6870_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_6854_ = lean_ctor_get(v_a_6850_, 0);
                lean_inc(v_fst_6854_);
                lean_dec(v_a_6850_);
                if lean_obj_tag(v_fst_6854_) == 0 {
                    if v_isShared_6853_ == 0 {
                        lean_ctor_set(v___x_6852_, 0, v___x_6847_);
                        v___x_6856_ = v___x_6852_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6857_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6857_, 0, v___x_6847_);
                        v___x_6856_ = v_reuseFailAlloc_6857_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_6858_ = lean_ctor_get(v_fst_6854_, 0);
                    lean_inc(v_val_6858_);
                    lean_dec_ref_known(v_fst_6854_, 1);
                    if v_isShared_6853_ == 0 {
                        lean_ctor_set(v___x_6852_, 0, v_val_6858_);
                        v___x_6860_ = v___x_6852_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6861_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6861_, 0, v_val_6858_);
                        v___x_6860_ = v_reuseFailAlloc_6861_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_6856_;
            }
            4 => {
                return v___x_6860_;
            }
            5 => {
                if v_isShared_6866_ == 0 {
                    v___x_6868_ = v___x_6865_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6869_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6869_, 0, v_a_6863_);
                    v___x_6868_ = v_reuseFailAlloc_6869_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6868_;
            }
            7 => {
                if v_isShared_6880_ == 0 {
                    v___x_6882_ = v___x_6879_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6883_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6883_, 0, v_a_6877_);
                    v___x_6882_ = v_reuseFailAlloc_6883_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6882_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___boxed(
    mut v_x_6885_: *mut LeanObject,
    mut v_c_6886_: *mut LeanObject,
    mut v_a_6887_: *mut LeanObject,
    mut v_a_6888_: *mut LeanObject,
    mut v_a_6889_: *mut LeanObject,
    mut v_a_6890_: *mut LeanObject,
    mut v_a_6891_: *mut LeanObject,
    mut v_a_6892_: *mut LeanObject,
    mut v_a_6893_: *mut LeanObject,
    mut v_a_6894_: *mut LeanObject,
    mut v_a_6895_: *mut LeanObject,
    mut v_a_6896_: *mut LeanObject,
    mut v_a_6897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6898_: *mut LeanObject = core::ptr::null_mut();
    v_res_6898_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_x_6885_, v_c_6886_, v_a_6887_, v_a_6888_, v_a_6889_, v_a_6890_, v_a_6891_, v_a_6892_, v_a_6893_, v_a_6894_, v_a_6895_, v_a_6896_);
    lean_dec(v_a_6896_);
    lean_dec_ref(v_a_6895_);
    lean_dec(v_a_6894_);
    lean_dec_ref(v_a_6893_);
    lean_dec(v_a_6892_);
    lean_dec_ref(v_a_6891_);
    lean_dec(v_a_6890_);
    lean_dec_ref(v_a_6889_);
    lean_dec(v_a_6888_);
    lean_dec(v_a_6887_);
    return v_res_6898_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(
    mut v_c_6899_: *mut LeanObject,
    mut v_x_6900_: *mut LeanObject,
    mut v_as_6901_: *mut LeanObject,
    mut v_sz_6902_: usize,
    mut v_i_6903_: usize,
    mut v_b_6904_: *mut LeanObject,
    mut v___y_6905_: *mut LeanObject,
    mut v___y_6906_: *mut LeanObject,
    mut v___y_6907_: *mut LeanObject,
    mut v___y_6908_: *mut LeanObject,
    mut v___y_6909_: *mut LeanObject,
    mut v___y_6910_: *mut LeanObject,
    mut v___y_6911_: *mut LeanObject,
    mut v___y_6912_: *mut LeanObject,
    mut v___y_6913_: *mut LeanObject,
    mut v___y_6914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6916_: *mut LeanObject = core::ptr::null_mut();
    v___x_6916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_6899_, v_x_6900_, v_as_6901_, v_sz_6902_, v_i_6903_, v_b_6904_, v___y_6905_);
    return v___x_6916_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_6917_: *mut LeanObject = *_args.add(0);
    let mut v_x_6918_: *mut LeanObject = *_args.add(1);
    let mut v_as_6919_: *mut LeanObject = *_args.add(2);
    let mut v_sz_6920_: *mut LeanObject = *_args.add(3);
    let mut v_i_6921_: *mut LeanObject = *_args.add(4);
    let mut v_b_6922_: *mut LeanObject = *_args.add(5);
    let mut v___y_6923_: *mut LeanObject = *_args.add(6);
    let mut v___y_6924_: *mut LeanObject = *_args.add(7);
    let mut v___y_6925_: *mut LeanObject = *_args.add(8);
    let mut v___y_6926_: *mut LeanObject = *_args.add(9);
    let mut v___y_6927_: *mut LeanObject = *_args.add(10);
    let mut v___y_6928_: *mut LeanObject = *_args.add(11);
    let mut v___y_6929_: *mut LeanObject = *_args.add(12);
    let mut v___y_6930_: *mut LeanObject = *_args.add(13);
    let mut v___y_6931_: *mut LeanObject = *_args.add(14);
    let mut v___y_6932_: *mut LeanObject = *_args.add(15);
    let mut v___y_6933_: *mut LeanObject = *_args.add(16);
    let mut v_sz_boxed_6934_: usize = 0;
    let mut v_i_boxed_6935_: usize = 0;
    let mut v_res_6936_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6934_ = lean_unbox_usize(v_sz_6920_);
    lean_dec(v_sz_6920_);
    v_i_boxed_6935_ = lean_unbox_usize(v_i_6921_);
    lean_dec(v_i_6921_);
    v_res_6936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(v_c_6917_, v_x_6918_, v_as_6919_, v_sz_boxed_6934_, v_i_boxed_6935_, v_b_6922_, v___y_6923_, v___y_6924_, v___y_6925_, v___y_6926_, v___y_6927_, v___y_6928_, v___y_6929_, v___y_6930_, v___y_6931_, v___y_6932_);
    lean_dec(v___y_6932_);
    lean_dec_ref(v___y_6931_);
    lean_dec(v___y_6930_);
    lean_dec_ref(v___y_6929_);
    lean_dec(v___y_6928_);
    lean_dec_ref(v___y_6927_);
    lean_dec(v___y_6926_);
    lean_dec_ref(v___y_6925_);
    lean_dec(v___y_6924_);
    lean_dec(v___y_6923_);
    lean_dec_ref(v_as_6919_);
    return v_res_6936_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(
    mut v_c_6937_: *mut LeanObject,
    mut v_x_6938_: *mut LeanObject,
    mut v_as_6939_: *mut LeanObject,
    mut v_sz_6940_: usize,
    mut v_i_6941_: usize,
    mut v_b_6942_: *mut LeanObject,
    mut v___y_6943_: *mut LeanObject,
    mut v___y_6944_: *mut LeanObject,
    mut v___y_6945_: *mut LeanObject,
    mut v___y_6946_: *mut LeanObject,
    mut v___y_6947_: *mut LeanObject,
    mut v___y_6948_: *mut LeanObject,
    mut v___y_6949_: *mut LeanObject,
    mut v___y_6950_: *mut LeanObject,
    mut v___y_6951_: *mut LeanObject,
    mut v___y_6952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6954_: *mut LeanObject = core::ptr::null_mut();
    v___x_6954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_6937_, v_x_6938_, v_as_6939_, v_sz_6940_, v_i_6941_, v_b_6942_, v___y_6943_);
    return v___x_6954_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_6955_: *mut LeanObject = *_args.add(0);
    let mut v_x_6956_: *mut LeanObject = *_args.add(1);
    let mut v_as_6957_: *mut LeanObject = *_args.add(2);
    let mut v_sz_6958_: *mut LeanObject = *_args.add(3);
    let mut v_i_6959_: *mut LeanObject = *_args.add(4);
    let mut v_b_6960_: *mut LeanObject = *_args.add(5);
    let mut v___y_6961_: *mut LeanObject = *_args.add(6);
    let mut v___y_6962_: *mut LeanObject = *_args.add(7);
    let mut v___y_6963_: *mut LeanObject = *_args.add(8);
    let mut v___y_6964_: *mut LeanObject = *_args.add(9);
    let mut v___y_6965_: *mut LeanObject = *_args.add(10);
    let mut v___y_6966_: *mut LeanObject = *_args.add(11);
    let mut v___y_6967_: *mut LeanObject = *_args.add(12);
    let mut v___y_6968_: *mut LeanObject = *_args.add(13);
    let mut v___y_6969_: *mut LeanObject = *_args.add(14);
    let mut v___y_6970_: *mut LeanObject = *_args.add(15);
    let mut v___y_6971_: *mut LeanObject = *_args.add(16);
    let mut v_sz_boxed_6972_: usize = 0;
    let mut v_i_boxed_6973_: usize = 0;
    let mut v_res_6974_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6972_ = lean_unbox_usize(v_sz_6958_);
    lean_dec(v_sz_6958_);
    v_i_boxed_6973_ = lean_unbox_usize(v_i_6959_);
    lean_dec(v_i_6959_);
    v_res_6974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(v_c_6955_, v_x_6956_, v_as_6957_, v_sz_boxed_6972_, v_i_boxed_6973_, v_b_6960_, v___y_6961_, v___y_6962_, v___y_6963_, v___y_6964_, v___y_6965_, v___y_6966_, v___y_6967_, v___y_6968_, v___y_6969_, v___y_6970_);
    lean_dec(v___y_6970_);
    lean_dec_ref(v___y_6969_);
    lean_dec(v___y_6968_);
    lean_dec_ref(v___y_6967_);
    lean_dec(v___y_6966_);
    lean_dec_ref(v___y_6965_);
    lean_dec(v___y_6964_);
    lean_dec_ref(v___y_6963_);
    lean_dec(v___y_6962_);
    lean_dec(v___y_6961_);
    lean_dec_ref(v_as_6957_);
    return v_res_6974_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(
    mut v_v_6975_: *mut LeanObject,
    mut v_a_6976_: *mut LeanObject,
    mut v___y_6977_: *mut LeanObject,
    mut v___y_6978_: *mut LeanObject,
    mut v___y_6979_: *mut LeanObject,
    mut v___y_6980_: *mut LeanObject,
    mut v___y_6981_: *mut LeanObject,
    mut v___y_6982_: *mut LeanObject,
    mut v___y_6983_: *mut LeanObject,
    mut v___y_6984_: *mut LeanObject,
    mut v___y_6985_: *mut LeanObject,
    mut v___y_6986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_6988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6991_: u8 = 0;
    let mut v___x_6992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6996_: u8 = 0;
    let mut v_val_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7010_: u8 = 0;
    let mut v_a_7011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7014_: u8 = 0;
    let mut v___x_7016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7018_: u8 = 0;
    let mut v_isSharedCheck_7019_: u8 = 0;
    let mut v_unused_7020_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_6988_ = lean_ctor_get(v_a_6976_, 1);
                v_isSharedCheck_7019_ = (!lean_is_exclusive(v_a_6976_)) as u8;
                if v_isSharedCheck_7019_ == 0 {
                    v_unused_7020_ = lean_ctor_get(v_a_6976_, 0);
                    lean_dec(v_unused_7020_);
                    v___x_6990_ = v_a_6976_;
                    v_isShared_6991_ = v_isSharedCheck_7019_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_6988_);
                    lean_dec(v_a_6976_);
                    v___x_6990_ = lean_box(0);
                    v_isShared_6991_ = v_isSharedCheck_7019_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_snd_6988_);
                lean_inc(v_v_6975_);
                v___x_6992_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_v_6975_, v_snd_6988_, v___y_6977_, v___y_6978_, v___y_6979_, v___y_6980_, v___y_6981_, v___y_6982_, v___y_6983_, v___y_6984_, v___y_6985_, v___y_6986_);
                if lean_obj_tag(v___x_6992_) == 0 {
                    v_a_6993_ = lean_ctor_get(v___x_6992_, 0);
                    v_isSharedCheck_7010_ = (!lean_is_exclusive(v___x_6992_)) as u8;
                    if v_isSharedCheck_7010_ == 0 {
                        v___x_6995_ = v___x_6992_;
                        v_isShared_6996_ = v_isSharedCheck_7010_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6993_);
                        lean_dec(v___x_6992_);
                        v___x_6995_ = lean_box(0);
                        v_isShared_6996_ = v_isSharedCheck_7010_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6990_);
                    lean_dec(v_snd_6988_);
                    lean_dec(v_v_6975_);
                    v_a_7011_ = lean_ctor_get(v___x_6992_, 0);
                    v_isSharedCheck_7018_ = (!lean_is_exclusive(v___x_6992_)) as u8;
                    if v_isSharedCheck_7018_ == 0 {
                        v___x_7013_ = v___x_6992_;
                        v_isShared_7014_ = v_isSharedCheck_7018_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_7011_);
                        lean_dec(v___x_6992_);
                        v___x_7013_ = lean_box(0);
                        v_isShared_7014_ = v_isSharedCheck_7018_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_6993_) == 1 {
                    lean_del_object(v___x_6995_);
                    lean_dec(v_snd_6988_);
                    v_val_6997_ = lean_ctor_get(v_a_6993_, 0);
                    lean_inc(v_val_6997_);
                    lean_dec_ref_known(v_a_6993_, 1);
                    v___x_6998_ = lean_box(0);
                    if v_isShared_6991_ == 0 {
                        lean_ctor_set(v___x_6990_, 1, v_val_6997_);
                        lean_ctor_set(v___x_6990_, 0, v___x_6998_);
                        v___x_7000_ = v___x_6990_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7002_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7002_, 0, v___x_6998_);
                        lean_ctor_set(v_reuseFailAlloc_7002_, 1, v_val_6997_);
                        v___x_7000_ = v_reuseFailAlloc_7002_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_6993_);
                    lean_dec(v_v_6975_);
                    lean_inc(v_snd_6988_);
                    v___x_7003_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7003_, 0, v_snd_6988_);
                    if v_isShared_6991_ == 0 {
                        lean_ctor_set(v___x_6990_, 0, v___x_7003_);
                        v___x_7005_ = v___x_6990_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7009_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7009_, 0, v___x_7003_);
                        lean_ctor_set(v_reuseFailAlloc_7009_, 1, v_snd_6988_);
                        v___x_7005_ = v_reuseFailAlloc_7009_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_a_6976_ = v___x_7000_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_6996_ == 0 {
                    lean_ctor_set(v___x_6995_, 0, v___x_7005_);
                    v___x_7007_ = v___x_6995_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7008_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7008_, 0, v___x_7005_);
                    v___x_7007_ = v_reuseFailAlloc_7008_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7007_;
            }
            6 => {
                if v_isShared_7014_ == 0 {
                    v___x_7016_ = v___x_7013_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7017_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7017_, 0, v_a_7011_);
                    v___x_7016_ = v_reuseFailAlloc_7017_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7016_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg___boxed(
    mut v_v_7021_: *mut LeanObject,
    mut v_a_7022_: *mut LeanObject,
    mut v___y_7023_: *mut LeanObject,
    mut v___y_7024_: *mut LeanObject,
    mut v___y_7025_: *mut LeanObject,
    mut v___y_7026_: *mut LeanObject,
    mut v___y_7027_: *mut LeanObject,
    mut v___y_7028_: *mut LeanObject,
    mut v___y_7029_: *mut LeanObject,
    mut v___y_7030_: *mut LeanObject,
    mut v___y_7031_: *mut LeanObject,
    mut v___y_7032_: *mut LeanObject,
    mut v___y_7033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7034_: *mut LeanObject = core::ptr::null_mut();
    v_res_7034_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_7021_, v_a_7022_, v___y_7023_, v___y_7024_, v___y_7025_, v___y_7026_, v___y_7027_, v___y_7028_, v___y_7029_, v___y_7030_, v___y_7031_, v___y_7032_);
    lean_dec(v___y_7032_);
    lean_dec_ref(v___y_7031_);
    lean_dec(v___y_7030_);
    lean_dec_ref(v___y_7029_);
    lean_dec(v___y_7028_);
    lean_dec_ref(v___y_7027_);
    lean_dec(v___y_7026_);
    lean_dec_ref(v___y_7025_);
    lean_dec(v___y_7024_);
    lean_dec(v___y_7023_);
    return v_res_7034_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(
    mut v_c_7035_: *mut LeanObject,
    mut v_a_7036_: *mut LeanObject,
    mut v_a_7037_: *mut LeanObject,
    mut v_a_7038_: *mut LeanObject,
    mut v_a_7039_: *mut LeanObject,
    mut v_a_7040_: *mut LeanObject,
    mut v_a_7041_: *mut LeanObject,
    mut v_a_7042_: *mut LeanObject,
    mut v_a_7043_: *mut LeanObject,
    mut v_a_7044_: *mut LeanObject,
    mut v_a_7045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_7047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7055_: u8 = 0;
    let mut v_fst_7056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7065_: u8 = 0;
    let mut v_a_7066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7069_: u8 = 0;
    let mut v___x_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7073_: u8 = 0;
    let mut v___x_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_7047_ = lean_ctor_get(v_c_7035_, 0);
                if lean_obj_tag(v_p_7047_) == 1 {
                    v_v_7048_ = lean_ctor_get(v_p_7047_, 1);
                    lean_inc(v_v_7048_);
                    v___x_7049_ = lean_box(0);
                    v___x_7050_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_7050_, 0, v___x_7049_);
                    lean_ctor_set(v___x_7050_, 1, v_c_7035_);
                    v___x_7051_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_7048_, v___x_7050_, v_a_7036_, v_a_7037_, v_a_7038_, v_a_7039_, v_a_7040_, v_a_7041_, v_a_7042_, v_a_7043_, v_a_7044_, v_a_7045_);
                    if lean_obj_tag(v___x_7051_) == 0 {
                        v_a_7052_ = lean_ctor_get(v___x_7051_, 0);
                        v_isSharedCheck_7065_ = (!lean_is_exclusive(v___x_7051_)) as u8;
                        if v_isSharedCheck_7065_ == 0 {
                            v___x_7054_ = v___x_7051_;
                            v_isShared_7055_ = v_isSharedCheck_7065_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7052_);
                            lean_dec(v___x_7051_);
                            v___x_7054_ = lean_box(0);
                            v_isShared_7055_ = v_isSharedCheck_7065_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_7066_ = lean_ctor_get(v___x_7051_, 0);
                        v_isSharedCheck_7073_ = (!lean_is_exclusive(v___x_7051_)) as u8;
                        if v_isSharedCheck_7073_ == 0 {
                            v___x_7068_ = v___x_7051_;
                            v_isShared_7069_ = v_isSharedCheck_7073_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_7066_);
                            lean_dec(v___x_7051_);
                            v___x_7068_ = lean_box(0);
                            v_isShared_7069_ = v_isSharedCheck_7073_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___x_7074_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(
                        v_c_7035_, v_a_7036_, v_a_7042_, v_a_7043_, v_a_7044_, v_a_7045_,
                    );
                    return v___x_7074_;
                }
            }
            1 => {
                v_fst_7056_ = lean_ctor_get(v_a_7052_, 0);
                if lean_obj_tag(v_fst_7056_) == 0 {
                    v_snd_7057_ = lean_ctor_get(v_a_7052_, 1);
                    lean_inc(v_snd_7057_);
                    lean_dec(v_a_7052_);
                    if v_isShared_7055_ == 0 {
                        lean_ctor_set(v___x_7054_, 0, v_snd_7057_);
                        v___x_7059_ = v___x_7054_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7060_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7060_, 0, v_snd_7057_);
                        v___x_7059_ = v_reuseFailAlloc_7060_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_7056_);
                    lean_dec(v_a_7052_);
                    v_val_7061_ = lean_ctor_get(v_fst_7056_, 0);
                    lean_inc(v_val_7061_);
                    lean_dec_ref_known(v_fst_7056_, 1);
                    if v_isShared_7055_ == 0 {
                        lean_ctor_set(v___x_7054_, 0, v_val_7061_);
                        v___x_7063_ = v___x_7054_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7064_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7064_, 0, v_val_7061_);
                        v___x_7063_ = v_reuseFailAlloc_7064_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7059_;
            }
            3 => {
                return v___x_7063_;
            }
            4 => {
                if v_isShared_7069_ == 0 {
                    v___x_7071_ = v___x_7068_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7072_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7072_, 0, v_a_7066_);
                    v___x_7071_ = v_reuseFailAlloc_7072_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq___boxed(
    mut v_c_7075_: *mut LeanObject,
    mut v_a_7076_: *mut LeanObject,
    mut v_a_7077_: *mut LeanObject,
    mut v_a_7078_: *mut LeanObject,
    mut v_a_7079_: *mut LeanObject,
    mut v_a_7080_: *mut LeanObject,
    mut v_a_7081_: *mut LeanObject,
    mut v_a_7082_: *mut LeanObject,
    mut v_a_7083_: *mut LeanObject,
    mut v_a_7084_: *mut LeanObject,
    mut v_a_7085_: *mut LeanObject,
    mut v_a_7086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7087_: *mut LeanObject = core::ptr::null_mut();
    v_res_7087_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_c_7075_, v_a_7076_, v_a_7077_, v_a_7078_, v_a_7079_, v_a_7080_, v_a_7081_, v_a_7082_, v_a_7083_, v_a_7084_, v_a_7085_);
    lean_dec(v_a_7085_);
    lean_dec_ref(v_a_7084_);
    lean_dec(v_a_7083_);
    lean_dec_ref(v_a_7082_);
    lean_dec(v_a_7081_);
    lean_dec_ref(v_a_7080_);
    lean_dec(v_a_7079_);
    lean_dec_ref(v_a_7078_);
    lean_dec(v_a_7077_);
    lean_dec(v_a_7076_);
    return v_res_7087_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(
    mut v_v_7088_: *mut LeanObject,
    mut v_inst_7089_: *mut LeanObject,
    mut v_a_7090_: *mut LeanObject,
    mut v___y_7091_: *mut LeanObject,
    mut v___y_7092_: *mut LeanObject,
    mut v___y_7093_: *mut LeanObject,
    mut v___y_7094_: *mut LeanObject,
    mut v___y_7095_: *mut LeanObject,
    mut v___y_7096_: *mut LeanObject,
    mut v___y_7097_: *mut LeanObject,
    mut v___y_7098_: *mut LeanObject,
    mut v___y_7099_: *mut LeanObject,
    mut v___y_7100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7102_: *mut LeanObject = core::ptr::null_mut();
    v___x_7102_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_7088_, v_a_7090_, v___y_7091_, v___y_7092_, v___y_7093_, v___y_7094_, v___y_7095_, v___y_7096_, v___y_7097_, v___y_7098_, v___y_7099_, v___y_7100_);
    return v___x_7102_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___boxed(
    mut v_v_7103_: *mut LeanObject,
    mut v_inst_7104_: *mut LeanObject,
    mut v_a_7105_: *mut LeanObject,
    mut v___y_7106_: *mut LeanObject,
    mut v___y_7107_: *mut LeanObject,
    mut v___y_7108_: *mut LeanObject,
    mut v___y_7109_: *mut LeanObject,
    mut v___y_7110_: *mut LeanObject,
    mut v___y_7111_: *mut LeanObject,
    mut v___y_7112_: *mut LeanObject,
    mut v___y_7113_: *mut LeanObject,
    mut v___y_7114_: *mut LeanObject,
    mut v___y_7115_: *mut LeanObject,
    mut v___y_7116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7117_: *mut LeanObject = core::ptr::null_mut();
    v_res_7117_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_7103_, v_inst_7104_, v_a_7105_, v___y_7106_, v___y_7107_, v___y_7108_, v___y_7109_, v___y_7110_, v___y_7111_, v___y_7112_, v___y_7113_, v___y_7114_, v___y_7115_);
    lean_dec(v___y_7115_);
    lean_dec_ref(v___y_7114_);
    lean_dec(v___y_7113_);
    lean_dec_ref(v___y_7112_);
    lean_dec(v___y_7111_);
    lean_dec_ref(v___y_7110_);
    lean_dec(v___y_7109_);
    lean_dec_ref(v___y_7108_);
    lean_dec(v___y_7107_);
    lean_dec(v___y_7106_);
    return v_res_7117_;
}
pub unsafe fn l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(
    mut v_a_7118_: *mut LeanObject,
    mut v_x_7119_: *mut LeanObject,
    mut v_x_7120_: usize,
    mut v_x_7121_: usize,
) -> *mut LeanObject {
    let mut v_cs_7122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_7123_: usize = 0;
    let mut v___x_7124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7126_: u8 = 0;
    let mut v___x_7128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7129_: u8 = 0;
    let mut v___x_7130_: usize = 0;
    let mut v___x_7131_: usize = 0;
    let mut v___x_7132_: usize = 0;
    let mut v_i_7133_: usize = 0;
    let mut v___x_7134_: usize = 0;
    let mut v_shift_7135_: usize = 0;
    let mut v_v_7136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_7138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7144_: u8 = 0;
    let mut v_unused_7145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_7146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: u8 = 0;
    let mut v___x_7151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7152_: u8 = 0;
    let mut v_v_7153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_7155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7161_: u8 = 0;
    let mut v_unused_7162_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7119_) == 0 {
                    v_cs_7122_ = lean_ctor_get(v_x_7119_, 0);
                    v_j_7123_ = lean_usize_shift_right(v_x_7120_, v_x_7121_);
                    v___x_7124_ = lean_usize_to_nat(v_j_7123_);
                    v___x_7125_ = lean_array_get_size(v_cs_7122_);
                    v___x_7126_ = lean_nat_dec_lt(v___x_7124_, v___x_7125_);
                    if v___x_7126_ == 0 {
                        lean_dec(v___x_7124_);
                        lean_dec_ref(v_a_7118_);
                        return v_x_7119_;
                    } else {
                        lean_inc_ref(v_cs_7122_);
                        v_isSharedCheck_7144_ = (!lean_is_exclusive(v_x_7119_)) as u8;
                        if v_isSharedCheck_7144_ == 0 {
                            v_unused_7145_ = lean_ctor_get(v_x_7119_, 0);
                            lean_dec(v_unused_7145_);
                            v___x_7128_ = v_x_7119_;
                            v_isShared_7129_ = v_isSharedCheck_7144_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_7119_);
                            v___x_7128_ = lean_box(0);
                            v_isShared_7129_ = v_isSharedCheck_7144_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_vs_7146_ = lean_ctor_get(v_x_7119_, 0);
                    v___x_7147_ = lean_usize_to_nat(v_x_7120_);
                    v___x_7148_ = lean_array_get_size(v_vs_7146_);
                    v___x_7149_ = lean_nat_dec_lt(v___x_7147_, v___x_7148_);
                    if v___x_7149_ == 0 {
                        lean_dec(v___x_7147_);
                        lean_dec_ref(v_a_7118_);
                        return v_x_7119_;
                    } else {
                        lean_inc_ref(v_vs_7146_);
                        v_isSharedCheck_7161_ = (!lean_is_exclusive(v_x_7119_)) as u8;
                        if v_isSharedCheck_7161_ == 0 {
                            v_unused_7162_ = lean_ctor_get(v_x_7119_, 0);
                            lean_dec(v_unused_7162_);
                            v___x_7151_ = v_x_7119_;
                            v_isShared_7152_ = v_isSharedCheck_7161_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v_x_7119_);
                            v___x_7151_ = lean_box(0);
                            v_isShared_7152_ = v_isSharedCheck_7161_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7130_ = 1usize;
                v___x_7131_ = lean_usize_shift_left(v___x_7130_, v_x_7121_);
                v___x_7132_ = lean_usize_sub(v___x_7131_, v___x_7130_);
                v_i_7133_ = lean_usize_land(v_x_7120_, v___x_7132_);
                v___x_7134_ = 5usize;
                v_shift_7135_ = lean_usize_sub(v_x_7121_, v___x_7134_);
                v_v_7136_ = lean_array_fget(v_cs_7122_, v___x_7124_);
                v___x_7137_ = lean_box(0);
                v_xs_x27_7138_ = lean_array_fset(v_cs_7122_, v___x_7124_, v___x_7137_);
                v___x_7139_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_7118_, v_v_7136_, v_i_7133_, v_shift_7135_);
                v___x_7140_ = lean_array_fset(v_xs_x27_7138_, v___x_7124_, v___x_7139_);
                lean_dec(v___x_7124_);
                if v_isShared_7129_ == 0 {
                    lean_ctor_set(v___x_7128_, 0, v___x_7140_);
                    v___x_7142_ = v___x_7128_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7143_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7143_, 0, v___x_7140_);
                    v___x_7142_ = v_reuseFailAlloc_7143_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7142_;
            }
            3 => {
                v_v_7153_ = lean_array_fget(v_vs_7146_, v___x_7147_);
                v___x_7154_ = lean_box(0);
                v_xs_x27_7155_ = lean_array_fset(v_vs_7146_, v___x_7147_, v___x_7154_);
                v___x_7156_ = l_Lean_PersistentArray_push___redArg(v_v_7153_, v_a_7118_);
                v___x_7157_ = lean_array_fset(v_xs_x27_7155_, v___x_7147_, v___x_7156_);
                lean_dec(v___x_7147_);
                if v_isShared_7152_ == 0 {
                    lean_ctor_set(v___x_7151_, 0, v___x_7157_);
                    v___x_7159_ = v___x_7151_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7160_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7160_, 0, v___x_7157_);
                    v___x_7159_ = v_reuseFailAlloc_7160_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7159_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___boxed(
    mut v_a_7163_: *mut LeanObject,
    mut v_x_7164_: *mut LeanObject,
    mut v_x_7165_: *mut LeanObject,
    mut v_x_7166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_93924__boxed_7167_: usize = 0;
    let mut v_x_93925__boxed_7168_: usize = 0;
    let mut v_res_7169_: *mut LeanObject = core::ptr::null_mut();
    v_x_93924__boxed_7167_ = lean_unbox_usize(v_x_7165_);
    lean_dec(v_x_7165_);
    v_x_93925__boxed_7168_ = lean_unbox_usize(v_x_7166_);
    lean_dec(v_x_7166_);
    v_res_7169_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_7163_, v_x_7164_, v_x_93924__boxed_7167_, v_x_93925__boxed_7168_);
    return v_res_7169_;
}
pub unsafe fn l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(
    mut v_a_7170_: *mut LeanObject,
    mut v_t_7171_: *mut LeanObject,
    mut v_i_7172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_7173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_7175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_7176_: usize = 0;
    let mut v_tailOff_7177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7180_: u8 = 0;
    let mut v___x_7181_: u8 = 0;
    let mut v___x_7182_: usize = 0;
    let mut v___x_7183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7189_: u8 = 0;
    let mut v___x_7191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_7195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7201_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_7173_ = lean_ctor_get(v_t_7171_, 0);
                v_tail_7174_ = lean_ctor_get(v_t_7171_, 1);
                v_size_7175_ = lean_ctor_get(v_t_7171_, 2);
                v_shift_7176_ = lean_ctor_get_usize(v_t_7171_, 4);
                v_tailOff_7177_ = lean_ctor_get(v_t_7171_, 3);
                v_isSharedCheck_7201_ = (!lean_is_exclusive(v_t_7171_)) as u8;
                if v_isSharedCheck_7201_ == 0 {
                    v___x_7179_ = v_t_7171_;
                    v_isShared_7180_ = v_isSharedCheck_7201_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_tailOff_7177_);
                    lean_inc(v_size_7175_);
                    lean_inc(v_tail_7174_);
                    lean_inc(v_root_7173_);
                    lean_dec(v_t_7171_);
                    v___x_7179_ = lean_box(0);
                    v_isShared_7180_ = v_isSharedCheck_7201_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7181_ = lean_nat_dec_le(v_tailOff_7177_, v_i_7172_);
                if v___x_7181_ == 0 {
                    v___x_7182_ = lean_usize_of_nat(v_i_7172_);
                    v___x_7183_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_7170_, v_root_7173_, v___x_7182_, v_shift_7176_);
                    if v_isShared_7180_ == 0 {
                        lean_ctor_set(v___x_7179_, 0, v___x_7183_);
                        v___x_7185_ = v___x_7179_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7186_ =
                            lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7186_, 0, v___x_7183_);
                        lean_ctor_set(v_reuseFailAlloc_7186_, 1, v_tail_7174_);
                        lean_ctor_set(v_reuseFailAlloc_7186_, 2, v_size_7175_);
                        lean_ctor_set(v_reuseFailAlloc_7186_, 3, v_tailOff_7177_);
                        lean_ctor_set_usize(v_reuseFailAlloc_7186_, 4, v_shift_7176_);
                        v___x_7185_ = v_reuseFailAlloc_7186_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_7187_ = lean_nat_sub(v_i_7172_, v_tailOff_7177_);
                    v___x_7188_ = lean_array_get_size(v_tail_7174_);
                    v___x_7189_ = lean_nat_dec_lt(v___x_7187_, v___x_7188_);
                    if v___x_7189_ == 0 {
                        lean_dec(v___x_7187_);
                        lean_dec_ref(v_a_7170_);
                        if v_isShared_7180_ == 0 {
                            v___x_7191_ = v___x_7179_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_7192_ =
                                lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                            lean_ctor_set(v_reuseFailAlloc_7192_, 0, v_root_7173_);
                            lean_ctor_set(v_reuseFailAlloc_7192_, 1, v_tail_7174_);
                            lean_ctor_set(v_reuseFailAlloc_7192_, 2, v_size_7175_);
                            lean_ctor_set(v_reuseFailAlloc_7192_, 3, v_tailOff_7177_);
                            lean_ctor_set_usize(v_reuseFailAlloc_7192_, 4, v_shift_7176_);
                            v___x_7191_ = v_reuseFailAlloc_7192_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_v_7193_ = lean_array_fget(v_tail_7174_, v___x_7187_);
                        v___x_7194_ = lean_box(0);
                        v_xs_x27_7195_ = lean_array_fset(v_tail_7174_, v___x_7187_, v___x_7194_);
                        v___x_7196_ = l_Lean_PersistentArray_push___redArg(v_v_7193_, v_a_7170_);
                        v___x_7197_ = lean_array_fset(v_xs_x27_7195_, v___x_7187_, v___x_7196_);
                        lean_dec(v___x_7187_);
                        if v_isShared_7180_ == 0 {
                            lean_ctor_set(v___x_7179_, 1, v___x_7197_);
                            v___x_7199_ = v___x_7179_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_7200_ =
                                lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                            lean_ctor_set(v_reuseFailAlloc_7200_, 0, v_root_7173_);
                            lean_ctor_set(v_reuseFailAlloc_7200_, 1, v___x_7197_);
                            lean_ctor_set(v_reuseFailAlloc_7200_, 2, v_size_7175_);
                            lean_ctor_set(v_reuseFailAlloc_7200_, 3, v_tailOff_7177_);
                            lean_ctor_set_usize(v_reuseFailAlloc_7200_, 4, v_shift_7176_);
                            v___x_7199_ = v_reuseFailAlloc_7200_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_7185_;
            }
            3 => {
                return v___x_7191_;
            }
            4 => {
                return v___x_7199_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0___boxed(
    mut v_a_7202_: *mut LeanObject,
    mut v_t_7203_: *mut LeanObject,
    mut v_i_7204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7205_: *mut LeanObject = core::ptr::null_mut();
    v_res_7205_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_7202_, v_t_7203_, v_i_7204_);
    lean_dec(v_i_7204_);
    return v_res_7205_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(
    mut v_a_7206_: *mut LeanObject,
    mut v_v_7207_: *mut LeanObject,
    mut v_s_7208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vars_7209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_7210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_x27_7211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_x27_7212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_7213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natDef_7214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dvds_7215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowers_7216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uppers_7217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_7218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_7219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_7220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_occurs_7221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_7222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextCnstrId_7223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_7224_: u8 = 0;
    let mut v_conflict_x3f_7225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_7226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_divMod_7227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntIds_7228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntInfos_7229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_7230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_7231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedCommRing_7232_: u8 = 0;
    let mut v_nonlinearOccs_7233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7236_: u8 = 0;
    let mut v___x_7237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_7209_ = lean_ctor_get(v_s_7208_, 0);
                v_varMap_7210_ = lean_ctor_get(v_s_7208_, 1);
                v_vars_x27_7211_ = lean_ctor_get(v_s_7208_, 2);
                v_varMap_x27_7212_ = lean_ctor_get(v_s_7208_, 3);
                v_natToIntMap_7213_ = lean_ctor_get(v_s_7208_, 4);
                v_natDef_7214_ = lean_ctor_get(v_s_7208_, 5);
                v_dvds_7215_ = lean_ctor_get(v_s_7208_, 6);
                v_lowers_7216_ = lean_ctor_get(v_s_7208_, 7);
                v_uppers_7217_ = lean_ctor_get(v_s_7208_, 8);
                v_diseqs_7218_ = lean_ctor_get(v_s_7208_, 9);
                v_elimEqs_7219_ = lean_ctor_get(v_s_7208_, 10);
                v_elimStack_7220_ = lean_ctor_get(v_s_7208_, 11);
                v_occurs_7221_ = lean_ctor_get(v_s_7208_, 12);
                v_assignment_7222_ = lean_ctor_get(v_s_7208_, 13);
                v_nextCnstrId_7223_ = lean_ctor_get(v_s_7208_, 14);
                v_caseSplits_7224_ = lean_ctor_get_uint8(
                    v_s_7208_,
                    (core::mem::size_of::<*mut LeanObject>() * 23) as u32,
                );
                v_conflict_x3f_7225_ = lean_ctor_get(v_s_7208_, 15);
                v_diseqSplits_7226_ = lean_ctor_get(v_s_7208_, 16);
                v_divMod_7227_ = lean_ctor_get(v_s_7208_, 17);
                v_toIntIds_7228_ = lean_ctor_get(v_s_7208_, 18);
                v_toIntInfos_7229_ = lean_ctor_get(v_s_7208_, 19);
                v_toIntTermMap_7230_ = lean_ctor_get(v_s_7208_, 20);
                v_toIntVarMap_7231_ = lean_ctor_get(v_s_7208_, 21);
                v_usedCommRing_7232_ = lean_ctor_get_uint8(
                    v_s_7208_,
                    (core::mem::size_of::<*mut LeanObject>() * 23 + 1) as u32,
                );
                v_nonlinearOccs_7233_ = lean_ctor_get(v_s_7208_, 22);
                v_isSharedCheck_7241_ = (!lean_is_exclusive(v_s_7208_)) as u8;
                if v_isSharedCheck_7241_ == 0 {
                    v___x_7235_ = v_s_7208_;
                    v_isShared_7236_ = v_isSharedCheck_7241_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nonlinearOccs_7233_);
                    lean_inc(v_toIntVarMap_7231_);
                    lean_inc(v_toIntTermMap_7230_);
                    lean_inc(v_toIntInfos_7229_);
                    lean_inc(v_toIntIds_7228_);
                    lean_inc(v_divMod_7227_);
                    lean_inc(v_diseqSplits_7226_);
                    lean_inc(v_conflict_x3f_7225_);
                    lean_inc(v_nextCnstrId_7223_);
                    lean_inc(v_assignment_7222_);
                    lean_inc(v_occurs_7221_);
                    lean_inc(v_elimStack_7220_);
                    lean_inc(v_elimEqs_7219_);
                    lean_inc(v_diseqs_7218_);
                    lean_inc(v_uppers_7217_);
                    lean_inc(v_lowers_7216_);
                    lean_inc(v_dvds_7215_);
                    lean_inc(v_natDef_7214_);
                    lean_inc(v_natToIntMap_7213_);
                    lean_inc(v_varMap_x27_7212_);
                    lean_inc(v_vars_x27_7211_);
                    lean_inc(v_varMap_7210_);
                    lean_inc(v_vars_7209_);
                    lean_dec(v_s_7208_);
                    v___x_7235_ = lean_box(0);
                    v_isShared_7236_ = v_isSharedCheck_7241_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7237_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_7206_, v_lowers_7216_, v_v_7207_);
                if v_isShared_7236_ == 0 {
                    lean_ctor_set(v___x_7235_, 7, v___x_7237_);
                    v___x_7239_ = v___x_7235_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7240_ = lean_alloc_ctor(0, 23, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 0, v_vars_7209_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 1, v_varMap_7210_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 2, v_vars_x27_7211_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 3, v_varMap_x27_7212_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 4, v_natToIntMap_7213_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 5, v_natDef_7214_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 6, v_dvds_7215_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 7, v___x_7237_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 8, v_uppers_7217_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 9, v_diseqs_7218_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 10, v_elimEqs_7219_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 11, v_elimStack_7220_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 12, v_occurs_7221_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 13, v_assignment_7222_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 14, v_nextCnstrId_7223_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 15, v_conflict_x3f_7225_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 16, v_diseqSplits_7226_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 17, v_divMod_7227_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 18, v_toIntIds_7228_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 19, v_toIntInfos_7229_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 20, v_toIntTermMap_7230_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 21, v_toIntVarMap_7231_);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 22, v_nonlinearOccs_7233_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7240_,
                        (core::mem::size_of::<*mut LeanObject>() * 23) as u32,
                        v_caseSplits_7224_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7240_,
                        (core::mem::size_of::<*mut LeanObject>() * 23 + 1) as u32,
                        v_usedCommRing_7232_,
                    );
                    v___x_7239_ = v_reuseFailAlloc_7240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed(
    mut v_a_7242_: *mut LeanObject,
    mut v_v_7243_: *mut LeanObject,
    mut v_s_7244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7245_: *mut LeanObject = core::ptr::null_mut();
    v_res_7245_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(v_a_7242_, v_v_7243_, v_s_7244_);
    lean_dec(v_v_7243_);
    return v_res_7245_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(
    mut v_a_7246_: *mut LeanObject,
    mut v_v_7247_: *mut LeanObject,
    mut v_s_7248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vars_7249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_7250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_x27_7251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_x27_7252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_7253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natDef_7254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dvds_7255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowers_7256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uppers_7257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_7258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_7259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_7260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_occurs_7261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_7262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextCnstrId_7263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_7264_: u8 = 0;
    let mut v_conflict_x3f_7265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_7266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_divMod_7267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntIds_7268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntInfos_7269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_7270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_7271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedCommRing_7272_: u8 = 0;
    let mut v_nonlinearOccs_7273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7276_: u8 = 0;
    let mut v___x_7277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7281_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_7249_ = lean_ctor_get(v_s_7248_, 0);
                v_varMap_7250_ = lean_ctor_get(v_s_7248_, 1);
                v_vars_x27_7251_ = lean_ctor_get(v_s_7248_, 2);
                v_varMap_x27_7252_ = lean_ctor_get(v_s_7248_, 3);
                v_natToIntMap_7253_ = lean_ctor_get(v_s_7248_, 4);
                v_natDef_7254_ = lean_ctor_get(v_s_7248_, 5);
                v_dvds_7255_ = lean_ctor_get(v_s_7248_, 6);
                v_lowers_7256_ = lean_ctor_get(v_s_7248_, 7);
                v_uppers_7257_ = lean_ctor_get(v_s_7248_, 8);
                v_diseqs_7258_ = lean_ctor_get(v_s_7248_, 9);
                v_elimEqs_7259_ = lean_ctor_get(v_s_7248_, 10);
                v_elimStack_7260_ = lean_ctor_get(v_s_7248_, 11);
                v_occurs_7261_ = lean_ctor_get(v_s_7248_, 12);
                v_assignment_7262_ = lean_ctor_get(v_s_7248_, 13);
                v_nextCnstrId_7263_ = lean_ctor_get(v_s_7248_, 14);
                v_caseSplits_7264_ = lean_ctor_get_uint8(
                    v_s_7248_,
                    (core::mem::size_of::<*mut LeanObject>() * 23) as u32,
                );
                v_conflict_x3f_7265_ = lean_ctor_get(v_s_7248_, 15);
                v_diseqSplits_7266_ = lean_ctor_get(v_s_7248_, 16);
                v_divMod_7267_ = lean_ctor_get(v_s_7248_, 17);
                v_toIntIds_7268_ = lean_ctor_get(v_s_7248_, 18);
                v_toIntInfos_7269_ = lean_ctor_get(v_s_7248_, 19);
                v_toIntTermMap_7270_ = lean_ctor_get(v_s_7248_, 20);
                v_toIntVarMap_7271_ = lean_ctor_get(v_s_7248_, 21);
                v_usedCommRing_7272_ = lean_ctor_get_uint8(
                    v_s_7248_,
                    (core::mem::size_of::<*mut LeanObject>() * 23 + 1) as u32,
                );
                v_nonlinearOccs_7273_ = lean_ctor_get(v_s_7248_, 22);
                v_isSharedCheck_7281_ = (!lean_is_exclusive(v_s_7248_)) as u8;
                if v_isSharedCheck_7281_ == 0 {
                    v___x_7275_ = v_s_7248_;
                    v_isShared_7276_ = v_isSharedCheck_7281_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nonlinearOccs_7273_);
                    lean_inc(v_toIntVarMap_7271_);
                    lean_inc(v_toIntTermMap_7270_);
                    lean_inc(v_toIntInfos_7269_);
                    lean_inc(v_toIntIds_7268_);
                    lean_inc(v_divMod_7267_);
                    lean_inc(v_diseqSplits_7266_);
                    lean_inc(v_conflict_x3f_7265_);
                    lean_inc(v_nextCnstrId_7263_);
                    lean_inc(v_assignment_7262_);
                    lean_inc(v_occurs_7261_);
                    lean_inc(v_elimStack_7260_);
                    lean_inc(v_elimEqs_7259_);
                    lean_inc(v_diseqs_7258_);
                    lean_inc(v_uppers_7257_);
                    lean_inc(v_lowers_7256_);
                    lean_inc(v_dvds_7255_);
                    lean_inc(v_natDef_7254_);
                    lean_inc(v_natToIntMap_7253_);
                    lean_inc(v_varMap_x27_7252_);
                    lean_inc(v_vars_x27_7251_);
                    lean_inc(v_varMap_7250_);
                    lean_inc(v_vars_7249_);
                    lean_dec(v_s_7248_);
                    v___x_7275_ = lean_box(0);
                    v_isShared_7276_ = v_isSharedCheck_7281_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7277_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_7246_, v_uppers_7257_, v_v_7247_);
                if v_isShared_7276_ == 0 {
                    lean_ctor_set(v___x_7275_, 8, v___x_7277_);
                    v___x_7279_ = v___x_7275_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7280_ = lean_alloc_ctor(0, 23, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 0, v_vars_7249_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 1, v_varMap_7250_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 2, v_vars_x27_7251_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 3, v_varMap_x27_7252_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 4, v_natToIntMap_7253_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 5, v_natDef_7254_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 6, v_dvds_7255_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 7, v_lowers_7256_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 8, v___x_7277_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 9, v_diseqs_7258_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 10, v_elimEqs_7259_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 11, v_elimStack_7260_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 12, v_occurs_7261_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 13, v_assignment_7262_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 14, v_nextCnstrId_7263_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 15, v_conflict_x3f_7265_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 16, v_diseqSplits_7266_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 17, v_divMod_7267_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 18, v_toIntIds_7268_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 19, v_toIntInfos_7269_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 20, v_toIntTermMap_7270_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 21, v_toIntVarMap_7271_);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 22, v_nonlinearOccs_7273_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7280_,
                        (core::mem::size_of::<*mut LeanObject>() * 23) as u32,
                        v_caseSplits_7264_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7280_,
                        (core::mem::size_of::<*mut LeanObject>() * 23 + 1) as u32,
                        v_usedCommRing_7272_,
                    );
                    v___x_7279_ = v_reuseFailAlloc_7280_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed(
    mut v_a_7282_: *mut LeanObject,
    mut v_v_7283_: *mut LeanObject,
    mut v_s_7284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7285_: *mut LeanObject = core::ptr::null_mut();
    v_res_7285_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(v_a_7282_, v_v_7283_, v_s_7284_);
    lean_dec(v_v_7283_);
    return v_res_7285_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3()
-> *mut LeanObject {
    let mut v___x_7293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7295_: *mut LeanObject = core::ptr::null_mut();
    v___x_7293_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2;
    v___x_7294_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5;
    v___x_7295_ = l_Lean_Name_append(v___x_7294_, v___x_7293_);
    return v___x_7295_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6()
-> *mut LeanObject {
    let mut v___x_7302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7304_: *mut LeanObject = core::ptr::null_mut();
    v___x_7302_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5;
    v___x_7303_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5;
    v___x_7304_ = l_Lean_Name_append(v___x_7303_, v___x_7302_);
    return v___x_7304_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9()
-> *mut LeanObject {
    let mut v___x_7311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7313_: *mut LeanObject = core::ptr::null_mut();
    v___x_7311_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8;
    v___x_7312_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5;
    v___x_7313_ = l_Lean_Name_append(v___x_7312_, v___x_7311_);
    return v___x_7313_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11()
-> *mut LeanObject {
    let mut v___x_7318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7320_: *mut LeanObject = core::ptr::null_mut();
    v___x_7318_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10;
    v___x_7319_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5;
    v___x_7320_ = l_Lean_Name_append(v___x_7319_, v___x_7318_);
    return v___x_7320_;
}
pub unsafe fn lean_grind_cutsat_assert_le(
    mut v_c_7321_: *mut LeanObject,
    mut v_a_7322_: *mut LeanObject,
    mut v_a_7323_: *mut LeanObject,
    mut v_a_7324_: *mut LeanObject,
    mut v_a_7325_: *mut LeanObject,
    mut v_a_7326_: *mut LeanObject,
    mut v_a_7327_: *mut LeanObject,
    mut v_a_7328_: *mut LeanObject,
    mut v_a_7329_: *mut LeanObject,
    mut v_a_7330_: *mut LeanObject,
    mut v_a_7331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7345_: u8 = 0;
    let mut v___x_7346_: u8 = 0;
    let mut v___x_7347_: u8 = 0;
    let mut v___x_7348_: u8 = 0;
    let mut v___x_7349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7354_: u8 = 0;
    let mut v_a_7355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7358_: u8 = 0;
    let mut v___x_7360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7362_: u8 = 0;
    let mut v___y_7364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_7374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7377_: u8 = 0;
    let mut v___x_7378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7398_: u8 = 0;
    let mut v___x_7399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7403_: u8 = 0;
    let mut v_unused_7404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7409_: u8 = 0;
    let mut v___x_7410_: u8 = 0;
    let mut v_options_7411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_7412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7413_: u8 = 0;
    let mut v___y_7415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_7428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7429_: u8 = 0;
    let mut v___x_7430_: u8 = 0;
    let mut v_k_7431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7437_: u8 = 0;
    let mut v___x_7438_: u8 = 0;
    let mut v___x_7439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_7440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_7442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7443_: u8 = 0;
    let mut v___f_7444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7448_: u8 = 0;
    let mut v___x_7449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7455_: u8 = 0;
    let mut v___x_7457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7459_: u8 = 0;
    let mut v_a_7460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7463_: u8 = 0;
    let mut v___x_7465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7467_: u8 = 0;
    let mut v___x_7468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7472_: u8 = 0;
    let mut v_a_7473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7476_: u8 = 0;
    let mut v___x_7478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7480_: u8 = 0;
    let mut v___x_7481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_7482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7483_: u8 = 0;
    let mut v_inheritedTraceOptions_7484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7487_: u8 = 0;
    let mut v___x_7488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7494_: u8 = 0;
    let mut v___x_7496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7498_: u8 = 0;
    let mut v_options_7499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7500_: u8 = 0;
    let mut v_inheritedTraceOptions_7501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7504_: u8 = 0;
    let mut v___x_7505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7511_: u8 = 0;
    let mut v___x_7513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7515_: u8 = 0;
    let mut v_a_7516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7519_: u8 = 0;
    let mut v___x_7521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7523_: u8 = 0;
    let mut v___x_7524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7526_: u8 = 0;
    let mut v___x_7527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7533_: u8 = 0;
    let mut v___x_7535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7537_: u8 = 0;
    let mut v___x_7538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7542_: u8 = 0;
    let mut v_a_7543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7546_: u8 = 0;
    let mut v___x_7548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7550_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7405_ =
                    l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_7322_, v_a_7330_);
                if lean_obj_tag(v___x_7405_) == 0 {
                    v_a_7406_ = lean_ctor_get(v___x_7405_, 0);
                    v_isSharedCheck_7542_ = (!lean_is_exclusive(v___x_7405_)) as u8;
                    if v_isSharedCheck_7542_ == 0 {
                        v___x_7408_ = v___x_7405_;
                        v_isShared_7409_ = v_isSharedCheck_7542_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_7406_);
                        lean_dec(v___x_7405_);
                        v___x_7408_ = lean_box(0);
                        v_isShared_7409_ = v_isSharedCheck_7542_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_dec(v_a_7331_);
                    lean_dec_ref(v_a_7330_);
                    lean_dec(v_a_7329_);
                    lean_dec_ref(v_a_7328_);
                    lean_dec(v_a_7327_);
                    lean_dec_ref(v_a_7326_);
                    lean_dec(v_a_7325_);
                    lean_dec_ref(v_a_7324_);
                    lean_dec(v_a_7323_);
                    lean_dec(v_a_7322_);
                    lean_dec_ref(v_c_7321_);
                    v_a_7543_ = lean_ctor_get(v___x_7405_, 0);
                    v_isSharedCheck_7550_ = (!lean_is_exclusive(v___x_7405_)) as u8;
                    if v_isSharedCheck_7550_ == 0 {
                        v___x_7545_ = v___x_7405_;
                        v_isShared_7546_ = v_isSharedCheck_7550_;
                        state = 30;
                        continue;
                    } else {
                        lean_inc(v_a_7543_);
                        lean_dec(v___x_7405_);
                        v___x_7545_ = lean_box(0);
                        v_isShared_7546_ = v_isSharedCheck_7550_;
                        state = 30;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7334_ = lean_box(0);
                v___x_7335_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7335_, 0, v___x_7334_);
                return v___x_7335_;
            }
            2 => {
                v___x_7341_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(
                    v___y_7338_,
                    v___y_7339_,
                    v___y_7340_,
                );
                lean_dec_ref(v___y_7340_);
                if lean_obj_tag(v___x_7341_) == 0 {
                    v_a_7342_ = lean_ctor_get(v___x_7341_, 0);
                    v_isSharedCheck_7354_ = (!lean_is_exclusive(v___x_7341_)) as u8;
                    if v_isSharedCheck_7354_ == 0 {
                        v___x_7344_ = v___x_7341_;
                        v_isShared_7345_ = v_isSharedCheck_7354_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7342_);
                        lean_dec(v___x_7341_);
                        v___x_7344_ = lean_box(0);
                        v_isShared_7345_ = v_isSharedCheck_7354_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___y_7339_);
                    lean_dec(v___y_7337_);
                    v_a_7355_ = lean_ctor_get(v___x_7341_, 0);
                    v_isSharedCheck_7362_ = (!lean_is_exclusive(v___x_7341_)) as u8;
                    if v_isSharedCheck_7362_ == 0 {
                        v___x_7357_ = v___x_7341_;
                        v_isShared_7358_ = v_isSharedCheck_7362_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7355_);
                        lean_dec(v___x_7341_);
                        v___x_7357_ = lean_box(0);
                        v_isShared_7358_ = v_isSharedCheck_7362_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_7346_ = 0;
                v___x_7347_ = (lean_unbox(v_a_7342_) as u8);
                lean_dec(v_a_7342_);
                v___x_7348_ = l_Lean_instBEqLBool_beq(v___x_7347_, v___x_7346_);
                if v___x_7348_ == 0 {
                    lean_dec(v___y_7339_);
                    lean_dec(v___y_7337_);
                    v___x_7349_ = lean_box(0);
                    if v_isShared_7345_ == 0 {
                        lean_ctor_set(v___x_7344_, 0, v___x_7349_);
                        v___x_7351_ = v___x_7344_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7352_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7352_, 0, v___x_7349_);
                        v___x_7351_ = v_reuseFailAlloc_7352_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7344_);
                    v___x_7353_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(
                        v___y_7337_,
                        v___y_7339_,
                    );
                    lean_dec(v___y_7339_);
                    return v___x_7353_;
                }
            }
            4 => {
                return v___x_7351_;
            }
            5 => {
                if v_isShared_7358_ == 0 {
                    v___x_7360_ = v___x_7357_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7361_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7361_, 0, v_a_7355_);
                    v___x_7360_ = v_reuseFailAlloc_7361_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7360_;
            }
            7 => {
                v_p_7374_ = lean_ctor_get(v___y_7366_, 0);
                lean_inc_ref(v_p_7374_);
                v___x_7375_ = l_Int_Linear_Poly_updateOccs___redArg(
                    v_p_7374_,
                    v___y_7369_,
                    v___y_7370_,
                    v___y_7371_,
                    v___y_7372_,
                    v___y_7373_,
                );
                lean_dec(v___y_7373_);
                lean_dec(v___y_7371_);
                lean_dec_ref(v___y_7370_);
                if lean_obj_tag(v___x_7375_) == 0 {
                    lean_dec_ref_known(v___x_7375_, 1);
                    v___x_7376_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9,
                    );
                    v___x_7377_ = lean_int_dec_lt(v___y_7365_, v___x_7376_);
                    lean_dec(v___y_7365_);
                    if v___x_7377_ == 0 {
                        lean_dec_ref(v___y_7367_);
                        v___x_7378_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                        v___x_7379_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_7378_, v___y_7368_, v___y_7369_);
                        if lean_obj_tag(v___x_7379_) == 0 {
                            lean_dec_ref_known(v___x_7379_, 1);
                            v___y_7337_ = v___y_7364_;
                            v___y_7338_ = v___y_7366_;
                            v___y_7339_ = v___y_7369_;
                            v___y_7340_ = v___y_7372_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec_ref(v___y_7372_);
                            lean_dec(v___y_7369_);
                            lean_dec_ref(v___y_7366_);
                            lean_dec(v___y_7364_);
                            return v___x_7379_;
                        }
                    } else {
                        lean_dec_ref(v___y_7368_);
                        v___x_7380_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                        v___x_7381_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_7380_, v___y_7367_, v___y_7369_);
                        if lean_obj_tag(v___x_7381_) == 0 {
                            lean_dec_ref_known(v___x_7381_, 1);
                            v___y_7337_ = v___y_7364_;
                            v___y_7338_ = v___y_7366_;
                            v___y_7339_ = v___y_7369_;
                            v___y_7340_ = v___y_7372_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec_ref(v___y_7372_);
                            lean_dec(v___y_7369_);
                            lean_dec_ref(v___y_7366_);
                            lean_dec(v___y_7364_);
                            return v___x_7381_;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_7372_);
                    lean_dec(v___y_7369_);
                    lean_dec_ref(v___y_7368_);
                    lean_dec_ref(v___y_7367_);
                    lean_dec_ref(v___y_7366_);
                    lean_dec(v___y_7365_);
                    lean_dec(v___y_7364_);
                    return v___x_7375_;
                }
            }
            8 => {
                v___x_7394_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7394_, 0, v___y_7383_);
                v___x_7395_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(
                    v___x_7394_,
                    v___y_7384_,
                    v___y_7385_,
                    v___y_7386_,
                    v___y_7387_,
                    v___y_7388_,
                    v___y_7389_,
                    v___y_7390_,
                    v___y_7391_,
                    v___y_7392_,
                    v___y_7393_,
                );
                lean_dec(v___y_7393_);
                lean_dec_ref(v___y_7392_);
                lean_dec(v___y_7391_);
                lean_dec_ref(v___y_7390_);
                lean_dec(v___y_7389_);
                lean_dec_ref(v___y_7388_);
                lean_dec(v___y_7387_);
                lean_dec_ref(v___y_7386_);
                lean_dec(v___y_7385_);
                lean_dec(v___y_7384_);
                if lean_obj_tag(v___x_7395_) == 0 {
                    v_isSharedCheck_7403_ = (!lean_is_exclusive(v___x_7395_)) as u8;
                    if v_isSharedCheck_7403_ == 0 {
                        v_unused_7404_ = lean_ctor_get(v___x_7395_, 0);
                        lean_dec(v_unused_7404_);
                        v___x_7397_ = v___x_7395_;
                        v_isShared_7398_ = v_isSharedCheck_7403_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec(v___x_7395_);
                        v___x_7397_ = lean_box(0);
                        v_isShared_7398_ = v_isSharedCheck_7403_;
                        state = 9;
                        continue;
                    }
                } else {
                    return v___x_7395_;
                }
            }
            9 => {
                v___x_7399_ = lean_box(0);
                if v_isShared_7398_ == 0 {
                    lean_ctor_set(v___x_7397_, 0, v___x_7399_);
                    v___x_7401_ = v___x_7397_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7402_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7402_, 0, v___x_7399_);
                    v___x_7401_ = v_reuseFailAlloc_7402_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7401_;
            }
            11 => {
                v___x_7410_ = (lean_unbox(v_a_7406_) as u8);
                lean_dec(v_a_7406_);
                if v___x_7410_ == 0 {
                    lean_del_object(v___x_7408_);
                    v_options_7411_ = lean_ctor_get(v_a_7330_, 2);
                    v_inheritedTraceOptions_7412_ = lean_ctor_get(v_a_7330_, 13);
                    v_hasTrace_7413_ = lean_ctor_get_uint8(
                        v_options_7411_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_7413_ == 0 {
                        v___y_7415_ = v_a_7322_;
                        v___y_7416_ = v_a_7323_;
                        v___y_7417_ = v_a_7324_;
                        v___y_7418_ = v_a_7325_;
                        v___y_7419_ = v_a_7326_;
                        v___y_7420_ = v_a_7327_;
                        v___y_7421_ = v_a_7328_;
                        v___y_7422_ = v_a_7329_;
                        v___y_7423_ = v_a_7330_;
                        v___y_7424_ = v_a_7331_;
                        state = 12;
                        continue;
                    } else {
                        v___x_7524_ =
                            l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10;
                        v___x_7525_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11,
                        );
                        v___x_7526_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_7412_,
                            v_options_7411_,
                            v___x_7525_,
                        );
                        if v___x_7526_ == 0 {
                            v___y_7415_ = v_a_7322_;
                            v___y_7416_ = v_a_7323_;
                            v___y_7417_ = v_a_7324_;
                            v___y_7418_ = v_a_7325_;
                            v___y_7419_ = v_a_7326_;
                            v___y_7420_ = v_a_7327_;
                            v___y_7421_ = v_a_7328_;
                            v___y_7422_ = v_a_7329_;
                            v___y_7423_ = v_a_7330_;
                            v___y_7424_ = v_a_7331_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc_ref(v_c_7321_);
                            v___x_7527_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
                                v_c_7321_, v_a_7322_, v_a_7330_,
                            );
                            if lean_obj_tag(v___x_7527_) == 0 {
                                v_a_7528_ = lean_ctor_get(v___x_7527_, 0);
                                lean_inc(v_a_7528_);
                                lean_dec_ref_known(v___x_7527_, 1);
                                v___x_7529_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_7524_, v_a_7528_, v_a_7328_, v_a_7329_, v_a_7330_, v_a_7331_);
                                if lean_obj_tag(v___x_7529_) == 0 {
                                    lean_dec_ref_known(v___x_7529_, 1);
                                    v___y_7415_ = v_a_7322_;
                                    v___y_7416_ = v_a_7323_;
                                    v___y_7417_ = v_a_7324_;
                                    v___y_7418_ = v_a_7325_;
                                    v___y_7419_ = v_a_7326_;
                                    v___y_7420_ = v_a_7327_;
                                    v___y_7421_ = v_a_7328_;
                                    v___y_7422_ = v_a_7329_;
                                    v___y_7423_ = v_a_7330_;
                                    v___y_7424_ = v_a_7331_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_dec(v_a_7331_);
                                    lean_dec_ref(v_a_7330_);
                                    lean_dec(v_a_7329_);
                                    lean_dec_ref(v_a_7328_);
                                    lean_dec(v_a_7327_);
                                    lean_dec_ref(v_a_7326_);
                                    lean_dec(v_a_7325_);
                                    lean_dec_ref(v_a_7324_);
                                    lean_dec(v_a_7323_);
                                    lean_dec(v_a_7322_);
                                    lean_dec_ref(v_c_7321_);
                                    return v___x_7529_;
                                }
                            } else {
                                lean_dec(v_a_7331_);
                                lean_dec_ref(v_a_7330_);
                                lean_dec(v_a_7329_);
                                lean_dec_ref(v_a_7328_);
                                lean_dec(v_a_7327_);
                                lean_dec_ref(v_a_7326_);
                                lean_dec(v_a_7325_);
                                lean_dec_ref(v_a_7324_);
                                lean_dec(v_a_7323_);
                                lean_dec(v_a_7322_);
                                lean_dec_ref(v_c_7321_);
                                v_a_7530_ = lean_ctor_get(v___x_7527_, 0);
                                v_isSharedCheck_7537_ = (!lean_is_exclusive(v___x_7527_)) as u8;
                                if v_isSharedCheck_7537_ == 0 {
                                    v___x_7532_ = v___x_7527_;
                                    v_isShared_7533_ = v_isSharedCheck_7537_;
                                    state = 27;
                                    continue;
                                } else {
                                    lean_inc(v_a_7530_);
                                    lean_dec(v___x_7527_);
                                    v___x_7532_ = lean_box(0);
                                    v_isShared_7533_ = v_isSharedCheck_7537_;
                                    state = 27;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_7331_);
                    lean_dec_ref(v_a_7330_);
                    lean_dec(v_a_7329_);
                    lean_dec_ref(v_a_7328_);
                    lean_dec(v_a_7327_);
                    lean_dec_ref(v_a_7326_);
                    lean_dec(v_a_7325_);
                    lean_dec_ref(v_a_7324_);
                    lean_dec(v_a_7323_);
                    lean_dec(v_a_7322_);
                    lean_dec_ref(v_c_7321_);
                    v___x_7538_ = lean_box(0);
                    if v_isShared_7409_ == 0 {
                        lean_ctor_set(v___x_7408_, 0, v___x_7538_);
                        v___x_7540_ = v___x_7408_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_7541_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7541_, 0, v___x_7538_);
                        v___x_7540_ = v_reuseFailAlloc_7541_;
                        state = 29;
                        continue;
                    }
                }
            }
            12 => {
                v___x_7425_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v_c_7321_);
                lean_inc_ref(v___y_7423_);
                v___x_7426_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(
                    v___x_7425_,
                    v___y_7415_,
                    v___y_7416_,
                    v___y_7417_,
                    v___y_7418_,
                    v___y_7419_,
                    v___y_7420_,
                    v___y_7421_,
                    v___y_7422_,
                    v___y_7423_,
                    v___y_7424_,
                );
                if lean_obj_tag(v___x_7426_) == 0 {
                    v_a_7427_ = lean_ctor_get(v___x_7426_, 0);
                    lean_inc(v_a_7427_);
                    lean_dec_ref_known(v___x_7426_, 1);
                    v_p_7428_ = lean_ctor_get(v_a_7427_, 0);
                    v___x_7429_ = l_Int_Linear_Poly_isUnsatLe(v_p_7428_);
                    if v___x_7429_ == 0 {
                        v___x_7430_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_a_7427_);
                        if v___x_7430_ == 0 {
                            if lean_obj_tag(v_p_7428_) == 1 {
                                v_k_7431_ = lean_ctor_get(v_p_7428_, 0);
                                lean_inc(v_k_7431_);
                                v_v_7432_ = lean_ctor_get(v_p_7428_, 1);
                                lean_inc(v_v_7432_);
                                lean_inc(v_a_7427_);
                                v___x_7433_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_a_7427_, v___y_7415_, v___y_7416_, v___y_7417_, v___y_7418_, v___y_7419_, v___y_7420_, v___y_7421_, v___y_7422_, v___y_7423_, v___y_7424_);
                                if lean_obj_tag(v___x_7433_) == 0 {
                                    v_a_7434_ = lean_ctor_get(v___x_7433_, 0);
                                    v_isSharedCheck_7472_ = (!lean_is_exclusive(v___x_7433_)) as u8;
                                    if v_isSharedCheck_7472_ == 0 {
                                        v___x_7436_ = v___x_7433_;
                                        v_isShared_7437_ = v_isSharedCheck_7472_;
                                        state = 13;
                                        continue;
                                    } else {
                                        lean_inc(v_a_7434_);
                                        lean_dec(v___x_7433_);
                                        v___x_7436_ = lean_box(0);
                                        v_isShared_7437_ = v_isSharedCheck_7472_;
                                        state = 13;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_v_7432_);
                                    lean_dec(v_k_7431_);
                                    lean_dec(v_a_7427_);
                                    lean_dec(v___y_7424_);
                                    lean_dec_ref(v___y_7423_);
                                    lean_dec(v___y_7422_);
                                    lean_dec_ref(v___y_7421_);
                                    lean_dec(v___y_7420_);
                                    lean_dec_ref(v___y_7419_);
                                    lean_dec(v___y_7418_);
                                    lean_dec_ref(v___y_7417_);
                                    lean_dec(v___y_7416_);
                                    lean_dec(v___y_7415_);
                                    v_a_7473_ = lean_ctor_get(v___x_7433_, 0);
                                    v_isSharedCheck_7480_ = (!lean_is_exclusive(v___x_7433_)) as u8;
                                    if v_isSharedCheck_7480_ == 0 {
                                        v___x_7475_ = v___x_7433_;
                                        v_isShared_7476_ = v_isSharedCheck_7480_;
                                        state = 19;
                                        continue;
                                    } else {
                                        lean_inc(v_a_7473_);
                                        lean_dec(v___x_7433_);
                                        v___x_7475_ = lean_box(0);
                                        v_isShared_7476_ = v_isSharedCheck_7480_;
                                        state = 19;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v___y_7420_);
                                lean_dec_ref(v___y_7419_);
                                lean_dec(v___y_7418_);
                                lean_dec_ref(v___y_7417_);
                                lean_dec(v___y_7416_);
                                v___x_7481_ =
                                    l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(
                                        v_a_7427_,
                                        v___y_7415_,
                                        v___y_7421_,
                                        v___y_7422_,
                                        v___y_7423_,
                                        v___y_7424_,
                                    );
                                lean_dec(v___y_7424_);
                                lean_dec_ref(v___y_7423_);
                                lean_dec(v___y_7422_);
                                lean_dec_ref(v___y_7421_);
                                lean_dec(v___y_7415_);
                                return v___x_7481_;
                            }
                        } else {
                            lean_dec(v___y_7420_);
                            lean_dec_ref(v___y_7419_);
                            lean_dec(v___y_7418_);
                            lean_dec_ref(v___y_7417_);
                            lean_dec(v___y_7416_);
                            v_options_7482_ = lean_ctor_get(v___y_7423_, 2);
                            v_hasTrace_7483_ = lean_ctor_get_uint8(
                                v_options_7482_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            );
                            if v_hasTrace_7483_ == 0 {
                                lean_dec(v_a_7427_);
                                lean_dec(v___y_7424_);
                                lean_dec_ref(v___y_7423_);
                                lean_dec(v___y_7422_);
                                lean_dec_ref(v___y_7421_);
                                lean_dec(v___y_7415_);
                                state = 1;
                                continue;
                            } else {
                                v_inheritedTraceOptions_7484_ = lean_ctor_get(v___y_7423_, 13);
                                v___x_7485_ =
                                    l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5;
                                v___x_7486_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6);
                                v___x_7487_ =
                                    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                        v_inheritedTraceOptions_7484_,
                                        v_options_7482_,
                                        v___x_7486_,
                                    );
                                if v___x_7487_ == 0 {
                                    lean_dec(v_a_7427_);
                                    lean_dec(v___y_7424_);
                                    lean_dec_ref(v___y_7423_);
                                    lean_dec(v___y_7422_);
                                    lean_dec_ref(v___y_7421_);
                                    lean_dec(v___y_7415_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_7488_ =
                                        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
                                            v_a_7427_,
                                            v___y_7415_,
                                            v___y_7423_,
                                        );
                                    lean_dec(v___y_7415_);
                                    if lean_obj_tag(v___x_7488_) == 0 {
                                        v_a_7489_ = lean_ctor_get(v___x_7488_, 0);
                                        lean_inc(v_a_7489_);
                                        lean_dec_ref_known(v___x_7488_, 1);
                                        v___x_7490_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_7485_, v_a_7489_, v___y_7421_, v___y_7422_, v___y_7423_, v___y_7424_);
                                        lean_dec(v___y_7424_);
                                        lean_dec_ref(v___y_7423_);
                                        lean_dec(v___y_7422_);
                                        lean_dec_ref(v___y_7421_);
                                        if lean_obj_tag(v___x_7490_) == 0 {
                                            lean_dec_ref_known(v___x_7490_, 1);
                                            state = 1;
                                            continue;
                                        } else {
                                            return v___x_7490_;
                                        }
                                    } else {
                                        lean_dec(v___y_7424_);
                                        lean_dec_ref(v___y_7423_);
                                        lean_dec(v___y_7422_);
                                        lean_dec_ref(v___y_7421_);
                                        v_a_7491_ = lean_ctor_get(v___x_7488_, 0);
                                        v_isSharedCheck_7498_ =
                                            (!lean_is_exclusive(v___x_7488_)) as u8;
                                        if v_isSharedCheck_7498_ == 0 {
                                            v___x_7493_ = v___x_7488_;
                                            v_isShared_7494_ = v_isSharedCheck_7498_;
                                            state = 21;
                                            continue;
                                        } else {
                                            lean_inc(v_a_7491_);
                                            lean_dec(v___x_7488_);
                                            v___x_7493_ = lean_box(0);
                                            v_isShared_7494_ = v_isSharedCheck_7498_;
                                            state = 21;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        v_options_7499_ = lean_ctor_get(v___y_7423_, 2);
                        v_hasTrace_7500_ = lean_ctor_get_uint8(
                            v_options_7499_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_7500_ == 0 {
                            v___y_7383_ = v_a_7427_;
                            v___y_7384_ = v___y_7415_;
                            v___y_7385_ = v___y_7416_;
                            v___y_7386_ = v___y_7417_;
                            v___y_7387_ = v___y_7418_;
                            v___y_7388_ = v___y_7419_;
                            v___y_7389_ = v___y_7420_;
                            v___y_7390_ = v___y_7421_;
                            v___y_7391_ = v___y_7422_;
                            v___y_7392_ = v___y_7423_;
                            v___y_7393_ = v___y_7424_;
                            state = 8;
                            continue;
                        } else {
                            v_inheritedTraceOptions_7501_ = lean_ctor_get(v___y_7423_, 13);
                            v___x_7502_ =
                                l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8;
                            v___x_7503_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9);
                            v___x_7504_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_7501_,
                                v_options_7499_,
                                v___x_7503_,
                            );
                            if v___x_7504_ == 0 {
                                v___y_7383_ = v_a_7427_;
                                v___y_7384_ = v___y_7415_;
                                v___y_7385_ = v___y_7416_;
                                v___y_7386_ = v___y_7417_;
                                v___y_7387_ = v___y_7418_;
                                v___y_7388_ = v___y_7419_;
                                v___y_7389_ = v___y_7420_;
                                v___y_7390_ = v___y_7421_;
                                v___y_7391_ = v___y_7422_;
                                v___y_7392_ = v___y_7423_;
                                v___y_7393_ = v___y_7424_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_7427_);
                                v___x_7505_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
                                    v_a_7427_,
                                    v___y_7415_,
                                    v___y_7423_,
                                );
                                if lean_obj_tag(v___x_7505_) == 0 {
                                    v_a_7506_ = lean_ctor_get(v___x_7505_, 0);
                                    lean_inc(v_a_7506_);
                                    lean_dec_ref_known(v___x_7505_, 1);
                                    v___x_7507_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_7502_, v_a_7506_, v___y_7421_, v___y_7422_, v___y_7423_, v___y_7424_);
                                    if lean_obj_tag(v___x_7507_) == 0 {
                                        lean_dec_ref_known(v___x_7507_, 1);
                                        v___y_7383_ = v_a_7427_;
                                        v___y_7384_ = v___y_7415_;
                                        v___y_7385_ = v___y_7416_;
                                        v___y_7386_ = v___y_7417_;
                                        v___y_7387_ = v___y_7418_;
                                        v___y_7388_ = v___y_7419_;
                                        v___y_7389_ = v___y_7420_;
                                        v___y_7390_ = v___y_7421_;
                                        v___y_7391_ = v___y_7422_;
                                        v___y_7392_ = v___y_7423_;
                                        v___y_7393_ = v___y_7424_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_dec(v_a_7427_);
                                        lean_dec(v___y_7424_);
                                        lean_dec_ref(v___y_7423_);
                                        lean_dec(v___y_7422_);
                                        lean_dec_ref(v___y_7421_);
                                        lean_dec(v___y_7420_);
                                        lean_dec_ref(v___y_7419_);
                                        lean_dec(v___y_7418_);
                                        lean_dec_ref(v___y_7417_);
                                        lean_dec(v___y_7416_);
                                        lean_dec(v___y_7415_);
                                        return v___x_7507_;
                                    }
                                } else {
                                    lean_dec(v_a_7427_);
                                    lean_dec(v___y_7424_);
                                    lean_dec_ref(v___y_7423_);
                                    lean_dec(v___y_7422_);
                                    lean_dec_ref(v___y_7421_);
                                    lean_dec(v___y_7420_);
                                    lean_dec_ref(v___y_7419_);
                                    lean_dec(v___y_7418_);
                                    lean_dec_ref(v___y_7417_);
                                    lean_dec(v___y_7416_);
                                    lean_dec(v___y_7415_);
                                    v_a_7508_ = lean_ctor_get(v___x_7505_, 0);
                                    v_isSharedCheck_7515_ = (!lean_is_exclusive(v___x_7505_)) as u8;
                                    if v_isSharedCheck_7515_ == 0 {
                                        v___x_7510_ = v___x_7505_;
                                        v_isShared_7511_ = v_isSharedCheck_7515_;
                                        state = 23;
                                        continue;
                                    } else {
                                        lean_inc(v_a_7508_);
                                        lean_dec(v___x_7505_);
                                        v___x_7510_ = lean_box(0);
                                        v_isShared_7511_ = v_isSharedCheck_7515_;
                                        state = 23;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    lean_dec(v___y_7424_);
                    lean_dec_ref(v___y_7423_);
                    lean_dec(v___y_7422_);
                    lean_dec_ref(v___y_7421_);
                    lean_dec(v___y_7420_);
                    lean_dec_ref(v___y_7419_);
                    lean_dec(v___y_7418_);
                    lean_dec_ref(v___y_7417_);
                    lean_dec(v___y_7416_);
                    lean_dec(v___y_7415_);
                    v_a_7516_ = lean_ctor_get(v___x_7426_, 0);
                    v_isSharedCheck_7523_ = (!lean_is_exclusive(v___x_7426_)) as u8;
                    if v_isSharedCheck_7523_ == 0 {
                        v___x_7518_ = v___x_7426_;
                        v_isShared_7519_ = v_isSharedCheck_7523_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_7516_);
                        lean_dec(v___x_7426_);
                        v___x_7518_ = lean_box(0);
                        v_isShared_7519_ = v_isSharedCheck_7523_;
                        state = 25;
                        continue;
                    }
                }
            }
            13 => {
                v___x_7438_ = (lean_unbox(v_a_7434_) as u8);
                lean_dec(v_a_7434_);
                if v___x_7438_ == 0 {
                    lean_del_object(v___x_7436_);
                    v___x_7439_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_a_7427_, v___y_7415_, v___y_7416_, v___y_7417_, v___y_7418_, v___y_7419_, v___y_7420_, v___y_7421_, v___y_7422_, v___y_7423_, v___y_7424_);
                    lean_dec(v___y_7420_);
                    lean_dec_ref(v___y_7419_);
                    lean_dec(v___y_7418_);
                    lean_dec_ref(v___y_7417_);
                    lean_dec(v___y_7416_);
                    if lean_obj_tag(v___x_7439_) == 0 {
                        v_options_7440_ = lean_ctor_get(v___y_7423_, 2);
                        v_a_7441_ = lean_ctor_get(v___x_7439_, 0);
                        lean_inc_n(v_a_7441_, 3);
                        lean_dec_ref_known(v___x_7439_, 1);
                        v_inheritedTraceOptions_7442_ = lean_ctor_get(v___y_7423_, 13);
                        v_hasTrace_7443_ = lean_ctor_get_uint8(
                            v_options_7440_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        lean_inc_n(v_v_7432_, 2);
                        v___f_7444_ = lean_alloc_closure(
                            l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        lean_closure_set(v___f_7444_, 0, v_a_7441_);
                        lean_closure_set(v___f_7444_, 1, v_v_7432_);
                        v___f_7445_ = lean_alloc_closure(
                            l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        lean_closure_set(v___f_7445_, 0, v_a_7441_);
                        lean_closure_set(v___f_7445_, 1, v_v_7432_);
                        if v_hasTrace_7443_ == 0 {
                            v___y_7364_ = v_v_7432_;
                            v___y_7365_ = v_k_7431_;
                            v___y_7366_ = v_a_7441_;
                            v___y_7367_ = v___f_7444_;
                            v___y_7368_ = v___f_7445_;
                            v___y_7369_ = v___y_7415_;
                            v___y_7370_ = v___y_7421_;
                            v___y_7371_ = v___y_7422_;
                            v___y_7372_ = v___y_7423_;
                            v___y_7373_ = v___y_7424_;
                            state = 7;
                            continue;
                        } else {
                            v___x_7446_ =
                                l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2;
                            v___x_7447_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3);
                            v___x_7448_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_7442_,
                                v_options_7440_,
                                v___x_7447_,
                            );
                            if v___x_7448_ == 0 {
                                v___y_7364_ = v_v_7432_;
                                v___y_7365_ = v_k_7431_;
                                v___y_7366_ = v_a_7441_;
                                v___y_7367_ = v___f_7444_;
                                v___y_7368_ = v___f_7445_;
                                v___y_7369_ = v___y_7415_;
                                v___y_7370_ = v___y_7421_;
                                v___y_7371_ = v___y_7422_;
                                v___y_7372_ = v___y_7423_;
                                v___y_7373_ = v___y_7424_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_7441_);
                                v___x_7449_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
                                    v_a_7441_,
                                    v___y_7415_,
                                    v___y_7423_,
                                );
                                if lean_obj_tag(v___x_7449_) == 0 {
                                    v_a_7450_ = lean_ctor_get(v___x_7449_, 0);
                                    lean_inc(v_a_7450_);
                                    lean_dec_ref_known(v___x_7449_, 1);
                                    v___x_7451_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_7446_, v_a_7450_, v___y_7421_, v___y_7422_, v___y_7423_, v___y_7424_);
                                    if lean_obj_tag(v___x_7451_) == 0 {
                                        lean_dec_ref_known(v___x_7451_, 1);
                                        v___y_7364_ = v_v_7432_;
                                        v___y_7365_ = v_k_7431_;
                                        v___y_7366_ = v_a_7441_;
                                        v___y_7367_ = v___f_7444_;
                                        v___y_7368_ = v___f_7445_;
                                        v___y_7369_ = v___y_7415_;
                                        v___y_7370_ = v___y_7421_;
                                        v___y_7371_ = v___y_7422_;
                                        v___y_7372_ = v___y_7423_;
                                        v___y_7373_ = v___y_7424_;
                                        state = 7;
                                        continue;
                                    } else {
                                        lean_dec_ref(v___f_7445_);
                                        lean_dec_ref(v___f_7444_);
                                        lean_dec(v_a_7441_);
                                        lean_dec(v_v_7432_);
                                        lean_dec(v_k_7431_);
                                        lean_dec(v___y_7424_);
                                        lean_dec_ref(v___y_7423_);
                                        lean_dec(v___y_7422_);
                                        lean_dec_ref(v___y_7421_);
                                        lean_dec(v___y_7415_);
                                        return v___x_7451_;
                                    }
                                } else {
                                    lean_dec_ref(v___f_7445_);
                                    lean_dec_ref(v___f_7444_);
                                    lean_dec(v_a_7441_);
                                    lean_dec(v_v_7432_);
                                    lean_dec(v_k_7431_);
                                    lean_dec(v___y_7424_);
                                    lean_dec_ref(v___y_7423_);
                                    lean_dec(v___y_7422_);
                                    lean_dec_ref(v___y_7421_);
                                    lean_dec(v___y_7415_);
                                    v_a_7452_ = lean_ctor_get(v___x_7449_, 0);
                                    v_isSharedCheck_7459_ = (!lean_is_exclusive(v___x_7449_)) as u8;
                                    if v_isSharedCheck_7459_ == 0 {
                                        v___x_7454_ = v___x_7449_;
                                        v_isShared_7455_ = v_isSharedCheck_7459_;
                                        state = 14;
                                        continue;
                                    } else {
                                        lean_inc(v_a_7452_);
                                        lean_dec(v___x_7449_);
                                        v___x_7454_ = lean_box(0);
                                        v_isShared_7455_ = v_isSharedCheck_7459_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_v_7432_);
                        lean_dec(v_k_7431_);
                        lean_dec(v___y_7424_);
                        lean_dec_ref(v___y_7423_);
                        lean_dec(v___y_7422_);
                        lean_dec_ref(v___y_7421_);
                        lean_dec(v___y_7415_);
                        v_a_7460_ = lean_ctor_get(v___x_7439_, 0);
                        v_isSharedCheck_7467_ = (!lean_is_exclusive(v___x_7439_)) as u8;
                        if v_isSharedCheck_7467_ == 0 {
                            v___x_7462_ = v___x_7439_;
                            v_isShared_7463_ = v_isSharedCheck_7467_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_7460_);
                            lean_dec(v___x_7439_);
                            v___x_7462_ = lean_box(0);
                            v_isShared_7463_ = v_isSharedCheck_7467_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_v_7432_);
                    lean_dec(v_k_7431_);
                    lean_dec(v_a_7427_);
                    lean_dec(v___y_7424_);
                    lean_dec_ref(v___y_7423_);
                    lean_dec(v___y_7422_);
                    lean_dec_ref(v___y_7421_);
                    lean_dec(v___y_7420_);
                    lean_dec_ref(v___y_7419_);
                    lean_dec(v___y_7418_);
                    lean_dec_ref(v___y_7417_);
                    lean_dec(v___y_7416_);
                    lean_dec(v___y_7415_);
                    v___x_7468_ = lean_box(0);
                    if v_isShared_7437_ == 0 {
                        lean_ctor_set(v___x_7436_, 0, v___x_7468_);
                        v___x_7470_ = v___x_7436_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_7471_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7471_, 0, v___x_7468_);
                        v___x_7470_ = v_reuseFailAlloc_7471_;
                        state = 18;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_7455_ == 0 {
                    v___x_7457_ = v___x_7454_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_7458_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7458_, 0, v_a_7452_);
                    v___x_7457_ = v_reuseFailAlloc_7458_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_7457_;
            }
            16 => {
                if v_isShared_7463_ == 0 {
                    v___x_7465_ = v___x_7462_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_7466_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7466_, 0, v_a_7460_);
                    v___x_7465_ = v_reuseFailAlloc_7466_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_7465_;
            }
            18 => {
                return v___x_7470_;
            }
            19 => {
                if v_isShared_7476_ == 0 {
                    v___x_7478_ = v___x_7475_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_7479_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7479_, 0, v_a_7473_);
                    v___x_7478_ = v_reuseFailAlloc_7479_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_7478_;
            }
            21 => {
                if v_isShared_7494_ == 0 {
                    v___x_7496_ = v___x_7493_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_7497_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7497_, 0, v_a_7491_);
                    v___x_7496_ = v_reuseFailAlloc_7497_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_7496_;
            }
            23 => {
                if v_isShared_7511_ == 0 {
                    v___x_7513_ = v___x_7510_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_7514_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7514_, 0, v_a_7508_);
                    v___x_7513_ = v_reuseFailAlloc_7514_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_7513_;
            }
            25 => {
                if v_isShared_7519_ == 0 {
                    v___x_7521_ = v___x_7518_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_7522_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7522_, 0, v_a_7516_);
                    v___x_7521_ = v_reuseFailAlloc_7522_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_7521_;
            }
            27 => {
                if v_isShared_7533_ == 0 {
                    v___x_7535_ = v___x_7532_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_7536_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7536_, 0, v_a_7530_);
                    v___x_7535_ = v_reuseFailAlloc_7536_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_7535_;
            }
            29 => {
                return v___x_7540_;
            }
            30 => {
                if v_isShared_7546_ == 0 {
                    v___x_7548_ = v___x_7545_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_7549_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7549_, 0, v_a_7543_);
                    v___x_7548_ = v_reuseFailAlloc_7549_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_7548_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___boxed(
    mut v_c_7551_: *mut LeanObject,
    mut v_a_7552_: *mut LeanObject,
    mut v_a_7553_: *mut LeanObject,
    mut v_a_7554_: *mut LeanObject,
    mut v_a_7555_: *mut LeanObject,
    mut v_a_7556_: *mut LeanObject,
    mut v_a_7557_: *mut LeanObject,
    mut v_a_7558_: *mut LeanObject,
    mut v_a_7559_: *mut LeanObject,
    mut v_a_7560_: *mut LeanObject,
    mut v_a_7561_: *mut LeanObject,
    mut v_a_7562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7563_: *mut LeanObject = core::ptr::null_mut();
    v_res_7563_ = lean_grind_cutsat_assert_le(
        v_c_7551_, v_a_7552_, v_a_7553_, v_a_7554_, v_a_7555_, v_a_7556_, v_a_7557_, v_a_7558_,
        v_a_7559_, v_a_7560_, v_a_7561_,
    );
    return v_res_7563_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_7565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7566_: *mut LeanObject = core::ptr::null_mut();
    v___x_7565_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0;
    v___x_7566_ = l_Lean_stringToMessageData(v___x_7565_);
    return v___x_7566_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(
    mut v_e_7567_: *mut LeanObject,
    mut v_a_7568_: *mut LeanObject,
    mut v_a_7569_: *mut LeanObject,
    mut v_a_7570_: *mut LeanObject,
    mut v_a_7571_: *mut LeanObject,
    mut v_a_7572_: *mut LeanObject,
    mut v_a_7573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7579_: u8 = 0;
    let mut v___x_7580_: u8 = 0;
    let mut v___x_7581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7589_: u8 = 0;
    let mut v_a_7590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7593_: u8 = 0;
    let mut v___x_7595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7575_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_7568_);
                if lean_obj_tag(v___x_7575_) == 0 {
                    v_a_7576_ = lean_ctor_get(v___x_7575_, 0);
                    v_isSharedCheck_7589_ = (!lean_is_exclusive(v___x_7575_)) as u8;
                    if v_isSharedCheck_7589_ == 0 {
                        v___x_7578_ = v___x_7575_;
                        v_isShared_7579_ = v_isSharedCheck_7589_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7576_);
                        lean_dec(v___x_7575_);
                        v___x_7578_ = lean_box(0);
                        v_isShared_7579_ = v_isSharedCheck_7589_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_7567_);
                    v_a_7590_ = lean_ctor_get(v___x_7575_, 0);
                    v_isSharedCheck_7597_ = (!lean_is_exclusive(v___x_7575_)) as u8;
                    if v_isSharedCheck_7597_ == 0 {
                        v___x_7592_ = v___x_7575_;
                        v_isShared_7593_ = v_isSharedCheck_7597_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7590_);
                        lean_dec(v___x_7575_);
                        v___x_7592_ = lean_box(0);
                        v_isShared_7593_ = v_isSharedCheck_7597_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7580_ = (lean_unbox(v_a_7576_) as u8);
                lean_dec(v_a_7576_);
                if v___x_7580_ == 0 {
                    lean_dec_ref(v_e_7567_);
                    v___x_7581_ = lean_box(0);
                    if v_isShared_7579_ == 0 {
                        lean_ctor_set(v___x_7578_, 0, v___x_7581_);
                        v___x_7583_ = v___x_7578_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7584_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7584_, 0, v___x_7581_);
                        v___x_7583_ = v_reuseFailAlloc_7584_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7578_);
                    v___x_7585_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1);
                    v___x_7586_ = l_Lean_indentExpr(v_e_7567_);
                    v___x_7587_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7587_, 0, v___x_7585_);
                    lean_ctor_set(v___x_7587_, 1, v___x_7586_);
                    v___x_7588_ = l_Lean_Meta_Sym_reportIssue(
                        v___x_7587_,
                        v_a_7568_,
                        v_a_7569_,
                        v_a_7570_,
                        v_a_7571_,
                        v_a_7572_,
                        v_a_7573_,
                    );
                    return v___x_7588_;
                }
            }
            2 => {
                return v___x_7583_;
            }
            3 => {
                if v_isShared_7593_ == 0 {
                    v___x_7595_ = v___x_7592_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7596_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7596_, 0, v_a_7590_);
                    v___x_7595_ = v_reuseFailAlloc_7596_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7595_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___boxed(
    mut v_e_7598_: *mut LeanObject,
    mut v_a_7599_: *mut LeanObject,
    mut v_a_7600_: *mut LeanObject,
    mut v_a_7601_: *mut LeanObject,
    mut v_a_7602_: *mut LeanObject,
    mut v_a_7603_: *mut LeanObject,
    mut v_a_7604_: *mut LeanObject,
    mut v_a_7605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7606_: *mut LeanObject = core::ptr::null_mut();
    v_res_7606_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_7598_, v_a_7599_, v_a_7600_, v_a_7601_, v_a_7602_, v_a_7603_, v_a_7604_);
    lean_dec(v_a_7604_);
    lean_dec_ref(v_a_7603_);
    lean_dec(v_a_7602_);
    lean_dec_ref(v_a_7601_);
    lean_dec(v_a_7600_);
    lean_dec_ref(v_a_7599_);
    return v_res_7606_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(
    mut v_e_7607_: *mut LeanObject,
    mut v_a_7608_: *mut LeanObject,
    mut v_a_7609_: *mut LeanObject,
    mut v_a_7610_: *mut LeanObject,
    mut v_a_7611_: *mut LeanObject,
    mut v_a_7612_: *mut LeanObject,
    mut v_a_7613_: *mut LeanObject,
    mut v_a_7614_: *mut LeanObject,
    mut v_a_7615_: *mut LeanObject,
    mut v_a_7616_: *mut LeanObject,
    mut v_a_7617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7619_: *mut LeanObject = core::ptr::null_mut();
    v___x_7619_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_7607_, v_a_7612_, v_a_7613_, v_a_7614_, v_a_7615_, v_a_7616_, v_a_7617_);
    return v___x_7619_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___boxed(
    mut v_e_7620_: *mut LeanObject,
    mut v_a_7621_: *mut LeanObject,
    mut v_a_7622_: *mut LeanObject,
    mut v_a_7623_: *mut LeanObject,
    mut v_a_7624_: *mut LeanObject,
    mut v_a_7625_: *mut LeanObject,
    mut v_a_7626_: *mut LeanObject,
    mut v_a_7627_: *mut LeanObject,
    mut v_a_7628_: *mut LeanObject,
    mut v_a_7629_: *mut LeanObject,
    mut v_a_7630_: *mut LeanObject,
    mut v_a_7631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7632_: *mut LeanObject = core::ptr::null_mut();
    v_res_7632_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(v_e_7620_, v_a_7621_, v_a_7622_, v_a_7623_, v_a_7624_, v_a_7625_, v_a_7626_, v_a_7627_, v_a_7628_, v_a_7629_, v_a_7630_);
    lean_dec(v_a_7630_);
    lean_dec_ref(v_a_7629_);
    lean_dec(v_a_7628_);
    lean_dec_ref(v_a_7627_);
    lean_dec(v_a_7626_);
    lean_dec_ref(v_a_7625_);
    lean_dec(v_a_7624_);
    lean_dec_ref(v_a_7623_);
    lean_dec(v_a_7622_);
    lean_dec(v_a_7621_);
    return v_res_7632_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(
    mut v_e_7638_: *mut LeanObject,
    mut v_a_7639_: *mut LeanObject,
    mut v_a_7640_: *mut LeanObject,
    mut v_a_7641_: *mut LeanObject,
    mut v_a_7642_: *mut LeanObject,
    mut v_a_7643_: *mut LeanObject,
    mut v_a_7644_: *mut LeanObject,
    mut v_a_7645_: *mut LeanObject,
    mut v_a_7646_: *mut LeanObject,
    mut v_a_7647_: *mut LeanObject,
    mut v_a_7648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7654_: u8 = 0;
    let mut v___x_7656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7661_: u8 = 0;
    let mut v_arg_7662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7664_: u8 = 0;
    let mut v_arg_7665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7667_: u8 = 0;
    let mut v_arg_7668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7670_: u8 = 0;
    let mut v___x_7671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7673_: u8 = 0;
    let mut v___x_7674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7678_: u8 = 0;
    let mut v___x_7679_: u8 = 0;
    let mut v___x_7680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7689_: u8 = 0;
    let mut v___x_7690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7691_: u8 = 0;
    let mut v___x_7692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7695_: u8 = 0;
    let mut v___x_7696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7700_: u8 = 0;
    let mut v_unused_7701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7705_: u8 = 0;
    let mut v___x_7707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7709_: u8 = 0;
    let mut v___x_7710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7714_: u8 = 0;
    let mut v___x_7716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7721_: u8 = 0;
    let mut v_a_7722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7725_: u8 = 0;
    let mut v___x_7727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7729_: u8 = 0;
    let mut v_isSharedCheck_7730_: u8 = 0;
    let mut v___x_7731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7734_: u8 = 0;
    let mut v___x_7735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7739_: u8 = 0;
    let mut v_unused_7740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7744_: u8 = 0;
    let mut v___x_7746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7748_: u8 = 0;
    let mut v_a_7749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7752_: u8 = 0;
    let mut v___x_7754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7756_: u8 = 0;
    let mut v_isSharedCheck_7757_: u8 = 0;
    let mut v_a_7758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7761_: u8 = 0;
    let mut v___x_7763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7765_: u8 = 0;
    let mut v_isSharedCheck_7766_: u8 = 0;
    let mut v_a_7767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7770_: u8 = 0;
    let mut v___x_7772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7774_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_7638_);
                v___x_7650_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_7638_, v_a_7646_);
                if lean_obj_tag(v___x_7650_) == 0 {
                    v_a_7651_ = lean_ctor_get(v___x_7650_, 0);
                    v_isSharedCheck_7766_ = (!lean_is_exclusive(v___x_7650_)) as u8;
                    if v_isSharedCheck_7766_ == 0 {
                        v___x_7653_ = v___x_7650_;
                        v_isShared_7654_ = v_isSharedCheck_7766_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7651_);
                        lean_dec(v___x_7650_);
                        v___x_7653_ = lean_box(0);
                        v_isShared_7654_ = v_isSharedCheck_7766_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_7638_);
                    v_a_7767_ = lean_ctor_get(v___x_7650_, 0);
                    v_isSharedCheck_7774_ = (!lean_is_exclusive(v___x_7650_)) as u8;
                    if v_isSharedCheck_7774_ == 0 {
                        v___x_7769_ = v___x_7650_;
                        v_isShared_7770_ = v_isSharedCheck_7774_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_a_7767_);
                        lean_dec(v___x_7650_);
                        v___x_7769_ = lean_box(0);
                        v_isShared_7770_ = v_isSharedCheck_7774_;
                        state = 24;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7660_ = l_Lean_Expr_cleanupAnnotations(v_a_7651_);
                v___x_7661_ = l_Lean_Expr_isApp(v___x_7660_);
                if v___x_7661_ == 0 {
                    lean_dec_ref(v___x_7660_);
                    lean_dec_ref(v_e_7638_);
                    state = 2;
                    continue;
                } else {
                    v_arg_7662_ = lean_ctor_get(v___x_7660_, 1);
                    lean_inc_ref(v_arg_7662_);
                    v___x_7663_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7660_);
                    v___x_7664_ = l_Lean_Expr_isApp(v___x_7663_);
                    if v___x_7664_ == 0 {
                        lean_dec_ref(v___x_7663_);
                        lean_dec_ref(v_arg_7662_);
                        lean_dec_ref(v_e_7638_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_7665_ = lean_ctor_get(v___x_7663_, 1);
                        lean_inc_ref(v_arg_7665_);
                        v___x_7666_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7663_);
                        v___x_7667_ = l_Lean_Expr_isApp(v___x_7666_);
                        if v___x_7667_ == 0 {
                            lean_dec_ref(v___x_7666_);
                            lean_dec_ref(v_arg_7665_);
                            lean_dec_ref(v_arg_7662_);
                            lean_dec_ref(v_e_7638_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_7668_ = lean_ctor_get(v___x_7666_, 1);
                            lean_inc_ref(v_arg_7668_);
                            v___x_7669_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7666_);
                            v___x_7670_ = l_Lean_Expr_isApp(v___x_7669_);
                            if v___x_7670_ == 0 {
                                lean_dec_ref(v___x_7669_);
                                lean_dec_ref(v_arg_7668_);
                                lean_dec_ref(v_arg_7665_);
                                lean_dec_ref(v_arg_7662_);
                                lean_dec_ref(v_e_7638_);
                                state = 2;
                                continue;
                            } else {
                                v___x_7671_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7669_);
                                v___x_7672_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2;
                                v___x_7673_ = l_Lean_Expr_isConstOf(v___x_7671_, v___x_7672_);
                                lean_dec_ref(v___x_7671_);
                                if v___x_7673_ == 0 {
                                    lean_dec_ref(v_arg_7668_);
                                    lean_dec_ref(v_arg_7665_);
                                    lean_dec_ref(v_arg_7662_);
                                    lean_dec_ref(v_e_7638_);
                                    state = 2;
                                    continue;
                                } else {
                                    lean_del_object(v___x_7653_);
                                    v___x_7674_ = l_Lean_Meta_Structural_isInstLEInt___redArg(
                                        v_arg_7668_,
                                        v_a_7646_,
                                    );
                                    if lean_obj_tag(v___x_7674_) == 0 {
                                        v_a_7675_ = lean_ctor_get(v___x_7674_, 0);
                                        v_isSharedCheck_7757_ =
                                            (!lean_is_exclusive(v___x_7674_)) as u8;
                                        if v_isSharedCheck_7757_ == 0 {
                                            v___x_7677_ = v___x_7674_;
                                            v_isShared_7678_ = v_isSharedCheck_7757_;
                                            state = 4;
                                            continue;
                                        } else {
                                            lean_inc(v_a_7675_);
                                            lean_dec(v___x_7674_);
                                            v___x_7677_ = lean_box(0);
                                            v_isShared_7678_ = v_isSharedCheck_7757_;
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref(v_arg_7665_);
                                        lean_dec_ref(v_arg_7662_);
                                        lean_dec_ref(v_e_7638_);
                                        v_a_7758_ = lean_ctor_get(v___x_7674_, 0);
                                        v_isSharedCheck_7765_ =
                                            (!lean_is_exclusive(v___x_7674_)) as u8;
                                        if v_isSharedCheck_7765_ == 0 {
                                            v___x_7760_ = v___x_7674_;
                                            v_isShared_7761_ = v_isSharedCheck_7765_;
                                            state = 22;
                                            continue;
                                        } else {
                                            lean_inc(v_a_7758_);
                                            lean_dec(v___x_7674_);
                                            v___x_7760_ = lean_box(0);
                                            v_isShared_7761_ = v_isSharedCheck_7765_;
                                            state = 22;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_7656_ = lean_box(0);
                if v_isShared_7654_ == 0 {
                    lean_ctor_set(v___x_7653_, 0, v___x_7656_);
                    v___x_7658_ = v___x_7653_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7659_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7659_, 0, v___x_7656_);
                    v___x_7658_ = v_reuseFailAlloc_7659_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7658_;
            }
            4 => {
                v___x_7679_ = (lean_unbox(v_a_7675_) as u8);
                lean_dec(v_a_7675_);
                if v___x_7679_ == 0 {
                    lean_dec_ref(v_arg_7665_);
                    lean_dec_ref(v_arg_7662_);
                    lean_dec_ref(v_e_7638_);
                    v___x_7680_ = lean_box(0);
                    if v_isShared_7678_ == 0 {
                        lean_ctor_set(v___x_7677_, 0, v___x_7680_);
                        v___x_7682_ = v___x_7677_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7683_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7683_, 0, v___x_7680_);
                        v___x_7682_ = v_reuseFailAlloc_7683_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7677_);
                    v___x_7684_ = l_Lean_Meta_getIntValue_x3f(
                        v_arg_7662_,
                        v_a_7645_,
                        v_a_7646_,
                        v_a_7647_,
                        v_a_7648_,
                    );
                    if lean_obj_tag(v___x_7684_) == 0 {
                        v_a_7685_ = lean_ctor_get(v___x_7684_, 0);
                        lean_inc(v_a_7685_);
                        lean_dec_ref_known(v___x_7684_, 1);
                        if lean_obj_tag(v_a_7685_) == 1 {
                            v_val_7686_ = lean_ctor_get(v_a_7685_, 0);
                            v_isSharedCheck_7730_ = (!lean_is_exclusive(v_a_7685_)) as u8;
                            if v_isSharedCheck_7730_ == 0 {
                                v___x_7688_ = v_a_7685_;
                                v_isShared_7689_ = v_isSharedCheck_7730_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_val_7686_);
                                lean_dec(v_a_7685_);
                                v___x_7688_ = lean_box(0);
                                v_isShared_7689_ = v_isSharedCheck_7730_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_7685_);
                            lean_dec_ref(v_arg_7665_);
                            v___x_7731_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_7638_, v_a_7643_, v_a_7644_, v_a_7645_, v_a_7646_, v_a_7647_, v_a_7648_);
                            if lean_obj_tag(v___x_7731_) == 0 {
                                v_isSharedCheck_7739_ = (!lean_is_exclusive(v___x_7731_)) as u8;
                                if v_isSharedCheck_7739_ == 0 {
                                    v_unused_7740_ = lean_ctor_get(v___x_7731_, 0);
                                    lean_dec(v_unused_7740_);
                                    v___x_7733_ = v___x_7731_;
                                    v_isShared_7734_ = v_isSharedCheck_7739_;
                                    state = 16;
                                    continue;
                                } else {
                                    lean_dec(v___x_7731_);
                                    v___x_7733_ = lean_box(0);
                                    v_isShared_7734_ = v_isSharedCheck_7739_;
                                    state = 16;
                                    continue;
                                }
                            } else {
                                v_a_7741_ = lean_ctor_get(v___x_7731_, 0);
                                v_isSharedCheck_7748_ = (!lean_is_exclusive(v___x_7731_)) as u8;
                                if v_isSharedCheck_7748_ == 0 {
                                    v___x_7743_ = v___x_7731_;
                                    v_isShared_7744_ = v_isSharedCheck_7748_;
                                    state = 18;
                                    continue;
                                } else {
                                    lean_inc(v_a_7741_);
                                    lean_dec(v___x_7731_);
                                    v___x_7743_ = lean_box(0);
                                    v_isShared_7744_ = v_isSharedCheck_7748_;
                                    state = 18;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_7665_);
                        lean_dec_ref(v_e_7638_);
                        v_a_7749_ = lean_ctor_get(v___x_7684_, 0);
                        v_isSharedCheck_7756_ = (!lean_is_exclusive(v___x_7684_)) as u8;
                        if v_isSharedCheck_7756_ == 0 {
                            v___x_7751_ = v___x_7684_;
                            v_isShared_7752_ = v_isSharedCheck_7756_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_a_7749_);
                            lean_dec(v___x_7684_);
                            v___x_7751_ = lean_box(0);
                            v_isShared_7752_ = v_isSharedCheck_7756_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_7682_;
            }
            6 => {
                v___x_7690_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9,
                );
                v___x_7691_ = lean_int_dec_eq(v_val_7686_, v___x_7690_);
                lean_dec(v_val_7686_);
                if v___x_7691_ == 0 {
                    lean_del_object(v___x_7688_);
                    lean_dec_ref(v_arg_7665_);
                    v___x_7692_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_7638_, v_a_7643_, v_a_7644_, v_a_7645_, v_a_7646_, v_a_7647_, v_a_7648_);
                    if lean_obj_tag(v___x_7692_) == 0 {
                        v_isSharedCheck_7700_ = (!lean_is_exclusive(v___x_7692_)) as u8;
                        if v_isSharedCheck_7700_ == 0 {
                            v_unused_7701_ = lean_ctor_get(v___x_7692_, 0);
                            lean_dec(v_unused_7701_);
                            v___x_7694_ = v___x_7692_;
                            v_isShared_7695_ = v_isSharedCheck_7700_;
                            state = 7;
                            continue;
                        } else {
                            lean_dec(v___x_7692_);
                            v___x_7694_ = lean_box(0);
                            v_isShared_7695_ = v_isSharedCheck_7700_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v_a_7702_ = lean_ctor_get(v___x_7692_, 0);
                        v_isSharedCheck_7709_ = (!lean_is_exclusive(v___x_7692_)) as u8;
                        if v_isSharedCheck_7709_ == 0 {
                            v___x_7704_ = v___x_7692_;
                            v_isShared_7705_ = v_isSharedCheck_7709_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_7702_);
                            lean_dec(v___x_7692_);
                            v___x_7704_ = lean_box(0);
                            v_isShared_7705_ = v_isSharedCheck_7709_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_7638_);
                    v___x_7710_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(
                        v_arg_7665_,
                        v_a_7639_,
                        v_a_7640_,
                        v_a_7641_,
                        v_a_7642_,
                        v_a_7643_,
                        v_a_7644_,
                        v_a_7645_,
                        v_a_7646_,
                        v_a_7647_,
                        v_a_7648_,
                    );
                    if lean_obj_tag(v___x_7710_) == 0 {
                        v_a_7711_ = lean_ctor_get(v___x_7710_, 0);
                        v_isSharedCheck_7721_ = (!lean_is_exclusive(v___x_7710_)) as u8;
                        if v_isSharedCheck_7721_ == 0 {
                            v___x_7713_ = v___x_7710_;
                            v_isShared_7714_ = v_isSharedCheck_7721_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_7711_);
                            lean_dec(v___x_7710_);
                            v___x_7713_ = lean_box(0);
                            v_isShared_7714_ = v_isSharedCheck_7721_;
                            state = 11;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_7688_);
                        v_a_7722_ = lean_ctor_get(v___x_7710_, 0);
                        v_isSharedCheck_7729_ = (!lean_is_exclusive(v___x_7710_)) as u8;
                        if v_isSharedCheck_7729_ == 0 {
                            v___x_7724_ = v___x_7710_;
                            v_isShared_7725_ = v_isSharedCheck_7729_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_7722_);
                            lean_dec(v___x_7710_);
                            v___x_7724_ = lean_box(0);
                            v_isShared_7725_ = v_isSharedCheck_7729_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            7 => {
                v___x_7696_ = lean_box(0);
                if v_isShared_7695_ == 0 {
                    lean_ctor_set(v___x_7694_, 0, v___x_7696_);
                    v___x_7698_ = v___x_7694_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7699_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7699_, 0, v___x_7696_);
                    v___x_7698_ = v_reuseFailAlloc_7699_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7698_;
            }
            9 => {
                if v_isShared_7705_ == 0 {
                    v___x_7707_ = v___x_7704_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7708_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7708_, 0, v_a_7702_);
                    v___x_7707_ = v_reuseFailAlloc_7708_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7707_;
            }
            11 => {
                if v_isShared_7689_ == 0 {
                    lean_ctor_set(v___x_7688_, 0, v_a_7711_);
                    v___x_7716_ = v___x_7688_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7720_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7720_, 0, v_a_7711_);
                    v___x_7716_ = v_reuseFailAlloc_7720_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_7714_ == 0 {
                    lean_ctor_set(v___x_7713_, 0, v___x_7716_);
                    v___x_7718_ = v___x_7713_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_7719_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7719_, 0, v___x_7716_);
                    v___x_7718_ = v_reuseFailAlloc_7719_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_7718_;
            }
            14 => {
                if v_isShared_7725_ == 0 {
                    v___x_7727_ = v___x_7724_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_7728_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7728_, 0, v_a_7722_);
                    v___x_7727_ = v_reuseFailAlloc_7728_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_7727_;
            }
            16 => {
                v___x_7735_ = lean_box(0);
                if v_isShared_7734_ == 0 {
                    lean_ctor_set(v___x_7733_, 0, v___x_7735_);
                    v___x_7737_ = v___x_7733_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_7738_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7738_, 0, v___x_7735_);
                    v___x_7737_ = v_reuseFailAlloc_7738_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_7737_;
            }
            18 => {
                if v_isShared_7744_ == 0 {
                    v___x_7746_ = v___x_7743_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_7747_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7747_, 0, v_a_7741_);
                    v___x_7746_ = v_reuseFailAlloc_7747_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_7746_;
            }
            20 => {
                if v_isShared_7752_ == 0 {
                    v___x_7754_ = v___x_7751_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_7755_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7755_, 0, v_a_7749_);
                    v___x_7754_ = v_reuseFailAlloc_7755_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_7754_;
            }
            22 => {
                if v_isShared_7761_ == 0 {
                    v___x_7763_ = v___x_7760_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_7764_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7764_, 0, v_a_7758_);
                    v___x_7763_ = v_reuseFailAlloc_7764_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_7763_;
            }
            24 => {
                if v_isShared_7770_ == 0 {
                    v___x_7772_ = v___x_7769_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_7773_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7773_, 0, v_a_7767_);
                    v___x_7772_ = v_reuseFailAlloc_7773_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_7772_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___boxed(
    mut v_e_7775_: *mut LeanObject,
    mut v_a_7776_: *mut LeanObject,
    mut v_a_7777_: *mut LeanObject,
    mut v_a_7778_: *mut LeanObject,
    mut v_a_7779_: *mut LeanObject,
    mut v_a_7780_: *mut LeanObject,
    mut v_a_7781_: *mut LeanObject,
    mut v_a_7782_: *mut LeanObject,
    mut v_a_7783_: *mut LeanObject,
    mut v_a_7784_: *mut LeanObject,
    mut v_a_7785_: *mut LeanObject,
    mut v_a_7786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7787_: *mut LeanObject = core::ptr::null_mut();
    v_res_7787_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_7775_, v_a_7776_, v_a_7777_, v_a_7778_, v_a_7779_, v_a_7780_, v_a_7781_, v_a_7782_, v_a_7783_, v_a_7784_, v_a_7785_);
    lean_dec(v_a_7785_);
    lean_dec_ref(v_a_7784_);
    lean_dec(v_a_7783_);
    lean_dec_ref(v_a_7782_);
    lean_dec(v_a_7781_);
    lean_dec_ref(v_a_7780_);
    lean_dec(v_a_7779_);
    lean_dec_ref(v_a_7778_);
    lean_dec(v_a_7777_);
    lean_dec(v_a_7776_);
    return v_res_7787_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(
    mut v_c_7788_: *mut LeanObject,
    mut v_a_7789_: *mut LeanObject,
    mut v_a_7790_: *mut LeanObject,
    mut v_a_7791_: *mut LeanObject,
    mut v_a_7792_: *mut LeanObject,
    mut v_a_7793_: *mut LeanObject,
    mut v_a_7794_: *mut LeanObject,
    mut v_a_7795_: *mut LeanObject,
    mut v_a_7796_: *mut LeanObject,
    mut v_a_7797_: *mut LeanObject,
    mut v_a_7798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_7800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7810_: u8 = 0;
    let mut v___x_7811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7816_: u8 = 0;
    let mut v___x_7817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7821_: u8 = 0;
    let mut v___x_7823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7825_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_7800_ = lean_ctor_get(v_c_7788_, 0);
                lean_inc_ref(v_p_7800_);
                v___x_7801_ = l_Int_Linear_Poly_normCommRing_x3f(
                    v_p_7800_, v_a_7789_, v_a_7790_, v_a_7791_, v_a_7792_, v_a_7793_, v_a_7794_,
                    v_a_7795_, v_a_7796_, v_a_7797_, v_a_7798_,
                );
                if lean_obj_tag(v___x_7801_) == 0 {
                    v_a_7802_ = lean_ctor_get(v___x_7801_, 0);
                    lean_inc(v_a_7802_);
                    lean_dec_ref_known(v___x_7801_, 1);
                    if lean_obj_tag(v_a_7802_) == 1 {
                        v_val_7803_ = lean_ctor_get(v_a_7802_, 0);
                        lean_inc(v_val_7803_);
                        lean_dec_ref_known(v_a_7802_, 1);
                        v_snd_7804_ = lean_ctor_get(v_val_7803_, 1);
                        lean_inc(v_snd_7804_);
                        v_fst_7805_ = lean_ctor_get(v_val_7803_, 0);
                        lean_inc(v_fst_7805_);
                        lean_dec(v_val_7803_);
                        v_fst_7806_ = lean_ctor_get(v_snd_7804_, 0);
                        v_snd_7807_ = lean_ctor_get(v_snd_7804_, 1);
                        v_isSharedCheck_7816_ = (!lean_is_exclusive(v_snd_7804_)) as u8;
                        if v_isSharedCheck_7816_ == 0 {
                            v___x_7809_ = v_snd_7804_;
                            v_isShared_7810_ = v_isSharedCheck_7816_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_7807_);
                            lean_inc(v_fst_7806_);
                            lean_dec(v_snd_7804_);
                            v___x_7809_ = lean_box(0);
                            v_isShared_7810_ = v_isSharedCheck_7816_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_7802_);
                        lean_inc(v_a_7798_);
                        lean_inc_ref(v_a_7797_);
                        lean_inc(v_a_7796_);
                        lean_inc_ref(v_a_7795_);
                        lean_inc(v_a_7794_);
                        lean_inc_ref(v_a_7793_);
                        lean_inc(v_a_7792_);
                        lean_inc_ref(v_a_7791_);
                        lean_inc(v_a_7790_);
                        lean_inc(v_a_7789_);
                        v___x_7817_ = lean_grind_cutsat_assert_le(
                            v_c_7788_, v_a_7789_, v_a_7790_, v_a_7791_, v_a_7792_, v_a_7793_,
                            v_a_7794_, v_a_7795_, v_a_7796_, v_a_7797_, v_a_7798_,
                        );
                        return v___x_7817_;
                    }
                } else {
                    lean_dec_ref(v_c_7788_);
                    v_a_7818_ = lean_ctor_get(v___x_7801_, 0);
                    v_isSharedCheck_7825_ = (!lean_is_exclusive(v___x_7801_)) as u8;
                    if v_isSharedCheck_7825_ == 0 {
                        v___x_7820_ = v___x_7801_;
                        v_isShared_7821_ = v_isSharedCheck_7825_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7818_);
                        lean_dec(v___x_7801_);
                        v___x_7820_ = lean_box(0);
                        v_isShared_7821_ = v_isSharedCheck_7825_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7811_ = lean_alloc_ctor(17, 3, (0) as u32);
                lean_ctor_set(v___x_7811_, 0, v_c_7788_);
                lean_ctor_set(v___x_7811_, 1, v_fst_7805_);
                lean_ctor_set(v___x_7811_, 2, v_fst_7806_);
                if v_isShared_7810_ == 0 {
                    lean_ctor_set(v___x_7809_, 1, v___x_7811_);
                    lean_ctor_set(v___x_7809_, 0, v_snd_7807_);
                    v___x_7813_ = v___x_7809_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7815_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7815_, 0, v_snd_7807_);
                    lean_ctor_set(v_reuseFailAlloc_7815_, 1, v___x_7811_);
                    v___x_7813_ = v_reuseFailAlloc_7815_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_a_7798_);
                lean_inc_ref(v_a_7797_);
                lean_inc(v_a_7796_);
                lean_inc_ref(v_a_7795_);
                lean_inc(v_a_7794_);
                lean_inc_ref(v_a_7793_);
                lean_inc(v_a_7792_);
                lean_inc_ref(v_a_7791_);
                lean_inc(v_a_7790_);
                lean_inc(v_a_7789_);
                v___x_7814_ = lean_grind_cutsat_assert_le(
                    v___x_7813_,
                    v_a_7789_,
                    v_a_7790_,
                    v_a_7791_,
                    v_a_7792_,
                    v_a_7793_,
                    v_a_7794_,
                    v_a_7795_,
                    v_a_7796_,
                    v_a_7797_,
                    v_a_7798_,
                );
                return v___x_7814_;
            }
            3 => {
                if v_isShared_7821_ == 0 {
                    v___x_7823_ = v___x_7820_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7824_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7824_, 0, v_a_7818_);
                    v___x_7823_ = v_reuseFailAlloc_7824_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7823_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore___boxed(
    mut v_c_7826_: *mut LeanObject,
    mut v_a_7827_: *mut LeanObject,
    mut v_a_7828_: *mut LeanObject,
    mut v_a_7829_: *mut LeanObject,
    mut v_a_7830_: *mut LeanObject,
    mut v_a_7831_: *mut LeanObject,
    mut v_a_7832_: *mut LeanObject,
    mut v_a_7833_: *mut LeanObject,
    mut v_a_7834_: *mut LeanObject,
    mut v_a_7835_: *mut LeanObject,
    mut v_a_7836_: *mut LeanObject,
    mut v_a_7837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7838_: *mut LeanObject = core::ptr::null_mut();
    v_res_7838_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v_c_7826_, v_a_7827_, v_a_7828_, v_a_7829_, v_a_7830_, v_a_7831_, v_a_7832_, v_a_7833_, v_a_7834_, v_a_7835_, v_a_7836_);
    lean_dec(v_a_7836_);
    lean_dec_ref(v_a_7835_);
    lean_dec(v_a_7834_);
    lean_dec_ref(v_a_7833_);
    lean_dec(v_a_7832_);
    lean_dec_ref(v_a_7831_);
    lean_dec(v_a_7830_);
    lean_dec_ref(v_a_7829_);
    lean_dec(v_a_7828_);
    lean_dec(v_a_7827_);
    return v_res_7838_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0() -> *mut LeanObject {
    let mut v___x_7839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7840_: *mut LeanObject = core::ptr::null_mut();
    v___x_7839_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
    v___x_7840_ = lean_int_neg(v___x_7839_);
    return v___x_7840_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(
    mut v_e_7841_: *mut LeanObject,
    mut v_eqTrue_7842_: u8,
    mut v_a_7843_: *mut LeanObject,
    mut v_a_7844_: *mut LeanObject,
    mut v_a_7845_: *mut LeanObject,
    mut v_a_7846_: *mut LeanObject,
    mut v_a_7847_: *mut LeanObject,
    mut v_a_7848_: *mut LeanObject,
    mut v_a_7849_: *mut LeanObject,
    mut v_a_7850_: *mut LeanObject,
    mut v_a_7851_: *mut LeanObject,
    mut v_a_7852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7858_: u8 = 0;
    let mut v_val_7859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7870_: u8 = 0;
    let mut v___x_7872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7876_: u8 = 0;
    let mut v___x_7877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7881_: u8 = 0;
    let mut v_a_7882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7885_: u8 = 0;
    let mut v___x_7887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7889_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_7841_);
                v___x_7854_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_7841_, v_a_7843_, v_a_7844_, v_a_7845_, v_a_7846_, v_a_7847_, v_a_7848_, v_a_7849_, v_a_7850_, v_a_7851_, v_a_7852_);
                if lean_obj_tag(v___x_7854_) == 0 {
                    v_a_7855_ = lean_ctor_get(v___x_7854_, 0);
                    v_isSharedCheck_7881_ = (!lean_is_exclusive(v___x_7854_)) as u8;
                    if v_isSharedCheck_7881_ == 0 {
                        v___x_7857_ = v___x_7854_;
                        v_isShared_7858_ = v_isSharedCheck_7881_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7855_);
                        lean_dec(v___x_7854_);
                        v___x_7857_ = lean_box(0);
                        v_isShared_7858_ = v_isSharedCheck_7881_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_7841_);
                    v_a_7882_ = lean_ctor_get(v___x_7854_, 0);
                    v_isSharedCheck_7889_ = (!lean_is_exclusive(v___x_7854_)) as u8;
                    if v_isSharedCheck_7889_ == 0 {
                        v___x_7884_ = v___x_7854_;
                        v_isShared_7885_ = v_isSharedCheck_7889_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7882_);
                        lean_dec(v___x_7854_);
                        v___x_7884_ = lean_box(0);
                        v_isShared_7885_ = v_isSharedCheck_7889_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_7855_) == 1 {
                    lean_del_object(v___x_7857_);
                    if v_eqTrue_7842_ == 0 {
                        v_val_7859_ = lean_ctor_get(v_a_7855_, 0);
                        lean_inc_n(v_val_7859_, 2);
                        lean_dec_ref_known(v_a_7855_, 1);
                        v___x_7860_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
                        v___x_7861_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0,
                        );
                        v___x_7862_ = l_Int_Linear_Poly_mul(v_val_7859_, v___x_7861_);
                        v___x_7863_ = l_Int_Linear_Poly_addConst(v___x_7862_, v___x_7860_);
                        v___x_7864_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_7864_, 0, v_e_7841_);
                        lean_ctor_set(v___x_7864_, 1, v_val_7859_);
                        v___x_7865_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_7865_, 0, v___x_7863_);
                        lean_ctor_set(v___x_7865_, 1, v___x_7864_);
                        v___x_7866_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_7865_, v_a_7843_, v_a_7844_, v_a_7845_, v_a_7846_, v_a_7847_, v_a_7848_, v_a_7849_, v_a_7850_, v_a_7851_, v_a_7852_);
                        return v___x_7866_;
                    } else {
                        v_val_7867_ = lean_ctor_get(v_a_7855_, 0);
                        v_isSharedCheck_7876_ = (!lean_is_exclusive(v_a_7855_)) as u8;
                        if v_isSharedCheck_7876_ == 0 {
                            v___x_7869_ = v_a_7855_;
                            v_isShared_7870_ = v_isSharedCheck_7876_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_7867_);
                            lean_dec(v_a_7855_);
                            v___x_7869_ = lean_box(0);
                            v_isShared_7870_ = v_isSharedCheck_7876_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_7855_);
                    lean_dec_ref(v_e_7841_);
                    v___x_7877_ = lean_box(0);
                    if v_isShared_7858_ == 0 {
                        lean_ctor_set(v___x_7857_, 0, v___x_7877_);
                        v___x_7879_ = v___x_7857_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7880_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7880_, 0, v___x_7877_);
                        v___x_7879_ = v_reuseFailAlloc_7880_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7870_ == 0 {
                    lean_ctor_set_tag(v___x_7869_, 0);
                    lean_ctor_set(v___x_7869_, 0, v_e_7841_);
                    v___x_7872_ = v___x_7869_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7875_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7875_, 0, v_e_7841_);
                    v___x_7872_ = v_reuseFailAlloc_7875_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7873_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7873_, 0, v_val_7867_);
                lean_ctor_set(v___x_7873_, 1, v___x_7872_);
                v___x_7874_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_7873_, v_a_7843_, v_a_7844_, v_a_7845_, v_a_7846_, v_a_7847_, v_a_7848_, v_a_7849_, v_a_7850_, v_a_7851_, v_a_7852_);
                return v___x_7874_;
            }
            4 => {
                return v___x_7879_;
            }
            5 => {
                if v_isShared_7885_ == 0 {
                    v___x_7887_ = v___x_7884_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7888_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7888_, 0, v_a_7882_);
                    v___x_7887_ = v_reuseFailAlloc_7888_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7887_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___boxed(
    mut v_e_7890_: *mut LeanObject,
    mut v_eqTrue_7891_: *mut LeanObject,
    mut v_a_7892_: *mut LeanObject,
    mut v_a_7893_: *mut LeanObject,
    mut v_a_7894_: *mut LeanObject,
    mut v_a_7895_: *mut LeanObject,
    mut v_a_7896_: *mut LeanObject,
    mut v_a_7897_: *mut LeanObject,
    mut v_a_7898_: *mut LeanObject,
    mut v_a_7899_: *mut LeanObject,
    mut v_a_7900_: *mut LeanObject,
    mut v_a_7901_: *mut LeanObject,
    mut v_a_7902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eqTrue_boxed_7903_: u8 = 0;
    let mut v_res_7904_: *mut LeanObject = core::ptr::null_mut();
    v_eqTrue_boxed_7903_ = (lean_unbox(v_eqTrue_7891_) as u8);
    v_res_7904_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(
        v_e_7890_,
        v_eqTrue_boxed_7903_,
        v_a_7892_,
        v_a_7893_,
        v_a_7894_,
        v_a_7895_,
        v_a_7896_,
        v_a_7897_,
        v_a_7898_,
        v_a_7899_,
        v_a_7900_,
        v_a_7901_,
    );
    lean_dec(v_a_7901_);
    lean_dec_ref(v_a_7900_);
    lean_dec(v_a_7899_);
    lean_dec_ref(v_a_7898_);
    lean_dec(v_a_7897_);
    lean_dec_ref(v_a_7896_);
    lean_dec(v_a_7895_);
    lean_dec_ref(v_a_7894_);
    lean_dec(v_a_7893_);
    lean_dec(v_a_7892_);
    return v_res_7904_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0() -> *mut LeanObject {
    let mut v___x_7905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7906_: *mut LeanObject = core::ptr::null_mut();
    v___x_7905_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
    v___x_7906_ = l_Lean_mkIntLit(v___x_7905_);
    return v___x_7906_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5() -> *mut LeanObject {
    let mut v___x_7914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7916_: *mut LeanObject = core::ptr::null_mut();
    v___x_7914_ = lean_box(0);
    v___x_7915_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4;
    v___x_7916_ = l_Lean_mkConst(v___x_7915_, v___x_7914_);
    return v___x_7916_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8() -> *mut LeanObject {
    let mut v___x_7922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7924_: *mut LeanObject = core::ptr::null_mut();
    v___x_7922_ = lean_box(0);
    v___x_7923_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7;
    v___x_7924_ = l_Lean_mkConst(v___x_7923_, v___x_7922_);
    return v___x_7924_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(
    mut v_e_7925_: *mut LeanObject,
    mut v_eqTrue_7926_: u8,
    mut v_a_7927_: *mut LeanObject,
    mut v_a_7928_: *mut LeanObject,
    mut v_a_7929_: *mut LeanObject,
    mut v_a_7930_: *mut LeanObject,
    mut v_a_7931_: *mut LeanObject,
    mut v_a_7932_: *mut LeanObject,
    mut v_a_7933_: *mut LeanObject,
    mut v_a_7934_: *mut LeanObject,
    mut v_a_7935_: *mut LeanObject,
    mut v_a_7936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7955_: u8 = 0;
    let mut v___x_7957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7959_: u8 = 0;
    let mut v_a_7960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7963_: u8 = 0;
    let mut v___x_7965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7967_: u8 = 0;
    let mut v___x_7969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7972_: u8 = 0;
    let mut v_arg_7973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7975_: u8 = 0;
    let mut v_arg_7976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7995_: u8 = 0;
    let mut v___x_7997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7999_: u8 = 0;
    let mut v_a_8000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8003_: u8 = 0;
    let mut v___x_8005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8007_: u8 = 0;
    let mut v_a_8008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8011_: u8 = 0;
    let mut v___x_8013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8015_: u8 = 0;
    let mut v___x_8016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8017_: u8 = 0;
    let mut v___x_8018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8019_: u8 = 0;
    let mut v___x_8020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8022_: u8 = 0;
    let mut v___x_8023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8024_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_7925_);
                v___x_7971_ = l_Lean_Expr_cleanupAnnotations(v_e_7925_);
                v___x_7972_ = l_Lean_Expr_isApp(v___x_7971_);
                if v___x_7972_ == 0 {
                    lean_dec_ref(v___x_7971_);
                    lean_dec_ref(v_e_7925_);
                    state = 6;
                    continue;
                } else {
                    v_arg_7973_ = lean_ctor_get(v___x_7971_, 1);
                    lean_inc_ref(v_arg_7973_);
                    v___x_7974_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7971_);
                    v___x_7975_ = l_Lean_Expr_isApp(v___x_7974_);
                    if v___x_7975_ == 0 {
                        lean_dec_ref(v___x_7974_);
                        lean_dec_ref(v_arg_7973_);
                        lean_dec_ref(v_e_7925_);
                        state = 6;
                        continue;
                    } else {
                        v_arg_7976_ = lean_ctor_get(v___x_7974_, 1);
                        lean_inc_ref(v_arg_7976_);
                        v___x_8016_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7974_);
                        v___x_8017_ = l_Lean_Expr_isApp(v___x_8016_);
                        if v___x_8017_ == 0 {
                            lean_dec_ref(v___x_8016_);
                            lean_dec_ref(v_arg_7976_);
                            lean_dec_ref(v_arg_7973_);
                            lean_dec_ref(v_e_7925_);
                            state = 6;
                            continue;
                        } else {
                            v___x_8018_ = l_Lean_Expr_appFnCleanup___redArg(v___x_8016_);
                            v___x_8019_ = l_Lean_Expr_isApp(v___x_8018_);
                            if v___x_8019_ == 0 {
                                lean_dec_ref(v___x_8018_);
                                lean_dec_ref(v_arg_7976_);
                                lean_dec_ref(v_arg_7973_);
                                lean_dec_ref(v_e_7925_);
                                state = 6;
                                continue;
                            } else {
                                v___x_8020_ = l_Lean_Expr_appFnCleanup___redArg(v___x_8018_);
                                v___x_8021_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2;
                                v___x_8022_ = l_Lean_Expr_isConstOf(v___x_8020_, v___x_8021_);
                                lean_dec_ref(v___x_8020_);
                                if v___x_8022_ == 0 {
                                    lean_dec_ref(v_arg_7976_);
                                    lean_dec_ref(v_arg_7973_);
                                    lean_dec_ref(v_e_7925_);
                                    state = 6;
                                    continue;
                                } else {
                                    if v_eqTrue_7926_ == 0 {
                                        v___x_8023_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5);
                                        v___y_7978_ = v___x_8023_;
                                        state = 7;
                                        continue;
                                    } else {
                                        v___x_8024_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8);
                                        v___y_7978_ = v___x_8024_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                lean_inc(v___y_7940_);
                v___x_7943_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(
                    v_fst_7941_,
                    v___y_7940_,
                    v_a_7927_,
                    v_a_7928_,
                    v_a_7929_,
                    v_a_7930_,
                    v_a_7931_,
                    v_a_7932_,
                    v_a_7933_,
                    v_a_7934_,
                    v_a_7935_,
                    v_a_7936_,
                );
                if lean_obj_tag(v___x_7943_) == 0 {
                    v_a_7944_ = lean_ctor_get(v___x_7943_, 0);
                    lean_inc(v_a_7944_);
                    lean_dec_ref_known(v___x_7943_, 1);
                    v___x_7945_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(
                        v_snd_7942_,
                        v___y_7940_,
                        v_a_7927_,
                        v_a_7928_,
                        v_a_7929_,
                        v_a_7930_,
                        v_a_7931_,
                        v_a_7932_,
                        v_a_7933_,
                        v_a_7934_,
                        v_a_7935_,
                        v_a_7936_,
                    );
                    if lean_obj_tag(v___x_7945_) == 0 {
                        v_a_7946_ = lean_ctor_get(v___x_7945_, 0);
                        lean_inc_n(v_a_7946_, 2);
                        lean_dec_ref_known(v___x_7945_, 1);
                        lean_inc(v_a_7944_);
                        v___x_7947_ = lean_alloc_ctor(3, 2, (0) as u32);
                        lean_ctor_set(v___x_7947_, 0, v_a_7944_);
                        lean_ctor_set(v___x_7947_, 1, v_a_7946_);
                        v___x_7948_ = l_Int_Linear_Expr_norm(v___x_7947_);
                        lean_dec_ref_known(v___x_7947_, 2);
                        v___x_7949_ = lean_alloc_ctor(2, 4, (1) as u32);
                        lean_ctor_set(v___x_7949_, 0, v_e_7925_);
                        lean_ctor_set(v___x_7949_, 1, v___y_7939_);
                        lean_ctor_set(v___x_7949_, 2, v_a_7944_);
                        lean_ctor_set(v___x_7949_, 3, v_a_7946_);
                        lean_ctor_set_uint8(
                            v___x_7949_,
                            (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                            v_eqTrue_7926_,
                        );
                        v___x_7950_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_7950_, 0, v___x_7948_);
                        lean_ctor_set(v___x_7950_, 1, v___x_7949_);
                        v___x_7951_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_7950_, v_a_7927_, v_a_7928_, v_a_7929_, v_a_7930_, v_a_7931_, v_a_7932_, v_a_7933_, v_a_7934_, v_a_7935_, v_a_7936_);
                        return v___x_7951_;
                    } else {
                        lean_dec(v_a_7944_);
                        lean_dec_ref(v___y_7939_);
                        lean_dec_ref(v_e_7925_);
                        v_a_7952_ = lean_ctor_get(v___x_7945_, 0);
                        v_isSharedCheck_7959_ = (!lean_is_exclusive(v___x_7945_)) as u8;
                        if v_isSharedCheck_7959_ == 0 {
                            v___x_7954_ = v___x_7945_;
                            v_isShared_7955_ = v_isSharedCheck_7959_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_7952_);
                            lean_dec(v___x_7945_);
                            v___x_7954_ = lean_box(0);
                            v_isShared_7955_ = v_isSharedCheck_7959_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_snd_7942_);
                    lean_dec(v___y_7940_);
                    lean_dec_ref(v___y_7939_);
                    lean_dec_ref(v_e_7925_);
                    v_a_7960_ = lean_ctor_get(v___x_7943_, 0);
                    v_isSharedCheck_7967_ = (!lean_is_exclusive(v___x_7943_)) as u8;
                    if v_isSharedCheck_7967_ == 0 {
                        v___x_7962_ = v___x_7943_;
                        v_isShared_7963_ = v_isSharedCheck_7967_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_7960_);
                        lean_dec(v___x_7943_);
                        v___x_7962_ = lean_box(0);
                        v_isShared_7963_ = v_isSharedCheck_7967_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7955_ == 0 {
                    v___x_7957_ = v___x_7954_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7958_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7958_, 0, v_a_7952_);
                    v___x_7957_ = v_reuseFailAlloc_7958_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7957_;
            }
            4 => {
                if v_isShared_7963_ == 0 {
                    v___x_7965_ = v___x_7962_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7966_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7966_, 0, v_a_7960_);
                    v___x_7965_ = v_reuseFailAlloc_7966_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7965_;
            }
            6 => {
                v___x_7969_ = lean_box(0);
                v___x_7970_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7970_, 0, v___x_7969_);
                return v___x_7970_;
            }
            7 => {
                v___x_7979_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_7925_, v_a_7927_);
                if lean_obj_tag(v___x_7979_) == 0 {
                    v_a_7980_ = lean_ctor_get(v___x_7979_, 0);
                    lean_inc(v_a_7980_);
                    lean_dec_ref_known(v___x_7979_, 1);
                    lean_inc_ref(v_arg_7976_);
                    v___x_7981_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(
                        v_arg_7976_,
                        v_a_7927_,
                        v_a_7928_,
                        v_a_7929_,
                        v_a_7930_,
                        v_a_7931_,
                        v_a_7932_,
                        v_a_7933_,
                        v_a_7934_,
                        v_a_7935_,
                        v_a_7936_,
                    );
                    if lean_obj_tag(v___x_7981_) == 0 {
                        v_a_7982_ = lean_ctor_get(v___x_7981_, 0);
                        lean_inc(v_a_7982_);
                        lean_dec_ref_known(v___x_7981_, 1);
                        v_fst_7983_ = lean_ctor_get(v_a_7982_, 0);
                        lean_inc(v_fst_7983_);
                        v_snd_7984_ = lean_ctor_get(v_a_7982_, 1);
                        lean_inc(v_snd_7984_);
                        lean_dec(v_a_7982_);
                        lean_inc_ref(v_arg_7973_);
                        v___x_7985_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(
                            v_arg_7973_,
                            v_a_7927_,
                            v_a_7928_,
                            v_a_7929_,
                            v_a_7930_,
                            v_a_7931_,
                            v_a_7932_,
                            v_a_7933_,
                            v_a_7934_,
                            v_a_7935_,
                            v_a_7936_,
                        );
                        if lean_obj_tag(v___x_7985_) == 0 {
                            v_a_7986_ = lean_ctor_get(v___x_7985_, 0);
                            lean_inc(v_a_7986_);
                            lean_dec_ref_known(v___x_7985_, 1);
                            v_fst_7987_ = lean_ctor_get(v_a_7986_, 0);
                            lean_inc_n(v_fst_7987_, 2);
                            v_snd_7988_ = lean_ctor_get(v_a_7986_, 1);
                            lean_inc(v_snd_7988_);
                            lean_dec(v_a_7986_);
                            lean_inc(v_fst_7983_);
                            lean_inc_ref(v___y_7978_);
                            v___x_7989_ = l_Lean_mkApp6(
                                v___y_7978_,
                                v_arg_7976_,
                                v_arg_7973_,
                                v_fst_7983_,
                                v_fst_7987_,
                                v_snd_7984_,
                                v_snd_7988_,
                            );
                            if v_eqTrue_7926_ == 0 {
                                v___x_7990_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
                                v___x_7991_ = l_Lean_mkIntAdd(v_fst_7987_, v___x_7990_);
                                v___y_7939_ = v___x_7989_;
                                v___y_7940_ = v_a_7980_;
                                v_fst_7941_ = v___x_7991_;
                                v_snd_7942_ = v_fst_7983_;
                                state = 1;
                                continue;
                            } else {
                                v___y_7939_ = v___x_7989_;
                                v___y_7940_ = v_a_7980_;
                                v_fst_7941_ = v_fst_7983_;
                                v_snd_7942_ = v_fst_7987_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_snd_7984_);
                            lean_dec(v_fst_7983_);
                            lean_dec(v_a_7980_);
                            lean_dec_ref(v_arg_7976_);
                            lean_dec_ref(v_arg_7973_);
                            lean_dec_ref(v_e_7925_);
                            v_a_7992_ = lean_ctor_get(v___x_7985_, 0);
                            v_isSharedCheck_7999_ = (!lean_is_exclusive(v___x_7985_)) as u8;
                            if v_isSharedCheck_7999_ == 0 {
                                v___x_7994_ = v___x_7985_;
                                v_isShared_7995_ = v_isSharedCheck_7999_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_7992_);
                                lean_dec(v___x_7985_);
                                v___x_7994_ = lean_box(0);
                                v_isShared_7995_ = v_isSharedCheck_7999_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_7980_);
                        lean_dec_ref(v_arg_7976_);
                        lean_dec_ref(v_arg_7973_);
                        lean_dec_ref(v_e_7925_);
                        v_a_8000_ = lean_ctor_get(v___x_7981_, 0);
                        v_isSharedCheck_8007_ = (!lean_is_exclusive(v___x_7981_)) as u8;
                        if v_isSharedCheck_8007_ == 0 {
                            v___x_8002_ = v___x_7981_;
                            v_isShared_8003_ = v_isSharedCheck_8007_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_8000_);
                            lean_dec(v___x_7981_);
                            v___x_8002_ = lean_box(0);
                            v_isShared_8003_ = v_isSharedCheck_8007_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_arg_7976_);
                    lean_dec_ref(v_arg_7973_);
                    lean_dec_ref(v_e_7925_);
                    v_a_8008_ = lean_ctor_get(v___x_7979_, 0);
                    v_isSharedCheck_8015_ = (!lean_is_exclusive(v___x_7979_)) as u8;
                    if v_isSharedCheck_8015_ == 0 {
                        v___x_8010_ = v___x_7979_;
                        v_isShared_8011_ = v_isSharedCheck_8015_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_8008_);
                        lean_dec(v___x_7979_);
                        v___x_8010_ = lean_box(0);
                        v_isShared_8011_ = v_isSharedCheck_8015_;
                        state = 12;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_7995_ == 0 {
                    v___x_7997_ = v___x_7994_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7998_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7998_, 0, v_a_7992_);
                    v___x_7997_ = v_reuseFailAlloc_7998_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7997_;
            }
            10 => {
                if v_isShared_8003_ == 0 {
                    v___x_8005_ = v___x_8002_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_8006_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8006_, 0, v_a_8000_);
                    v___x_8005_ = v_reuseFailAlloc_8006_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_8005_;
            }
            12 => {
                if v_isShared_8011_ == 0 {
                    v___x_8013_ = v___x_8010_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_8014_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8014_, 0, v_a_8008_);
                    v___x_8013_ = v_reuseFailAlloc_8014_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_8013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___boxed(
    mut v_e_8025_: *mut LeanObject,
    mut v_eqTrue_8026_: *mut LeanObject,
    mut v_a_8027_: *mut LeanObject,
    mut v_a_8028_: *mut LeanObject,
    mut v_a_8029_: *mut LeanObject,
    mut v_a_8030_: *mut LeanObject,
    mut v_a_8031_: *mut LeanObject,
    mut v_a_8032_: *mut LeanObject,
    mut v_a_8033_: *mut LeanObject,
    mut v_a_8034_: *mut LeanObject,
    mut v_a_8035_: *mut LeanObject,
    mut v_a_8036_: *mut LeanObject,
    mut v_a_8037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eqTrue_boxed_8038_: u8 = 0;
    let mut v_res_8039_: *mut LeanObject = core::ptr::null_mut();
    v_eqTrue_boxed_8038_ = (lean_unbox(v_eqTrue_8026_) as u8);
    v_res_8039_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(
        v_e_8025_,
        v_eqTrue_boxed_8038_,
        v_a_8027_,
        v_a_8028_,
        v_a_8029_,
        v_a_8030_,
        v_a_8031_,
        v_a_8032_,
        v_a_8033_,
        v_a_8034_,
        v_a_8035_,
        v_a_8036_,
    );
    lean_dec(v_a_8036_);
    lean_dec_ref(v_a_8035_);
    lean_dec(v_a_8034_);
    lean_dec_ref(v_a_8033_);
    lean_dec(v_a_8032_);
    lean_dec_ref(v_a_8031_);
    lean_dec(v_a_8030_);
    lean_dec_ref(v_a_8029_);
    lean_dec(v_a_8028_);
    lean_dec(v_a_8027_);
    return v_res_8039_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(
    mut v_e_8040_: *mut LeanObject,
    mut v_eqTrue_8041_: u8,
    mut v_a_8042_: *mut LeanObject,
    mut v_a_8043_: *mut LeanObject,
    mut v_a_8044_: *mut LeanObject,
    mut v_a_8045_: *mut LeanObject,
    mut v_a_8046_: *mut LeanObject,
    mut v_a_8047_: *mut LeanObject,
    mut v_a_8048_: *mut LeanObject,
    mut v_a_8049_: *mut LeanObject,
    mut v_a_8050_: *mut LeanObject,
    mut v_a_8051_: *mut LeanObject,
    mut v_a_8052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8084_: u8 = 0;
    let mut v___x_8086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8088_: u8 = 0;
    let mut v_a_8089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8092_: u8 = 0;
    let mut v___x_8094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8096_: u8 = 0;
    let mut v_____x_8098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8112_: u8 = 0;
    let mut v_arg_8113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8115_: u8 = 0;
    let mut v_arg_8116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8118_: u8 = 0;
    let mut v___x_8119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8120_: u8 = 0;
    let mut v___x_8121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8123_: u8 = 0;
    let mut v___x_8124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8140_: u8 = 0;
    let mut v___x_8142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8144_: u8 = 0;
    let mut v_a_8145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8148_: u8 = 0;
    let mut v___x_8150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8152_: u8 = 0;
    let mut v_a_8153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8156_: u8 = 0;
    let mut v___x_8158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8160_: u8 = 0;
    let mut v___x_8161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8168_: u8 = 0;
    let mut v___x_8170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8172_: u8 = 0;
    let mut v___x_8173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8178_: u8 = 0;
    let mut v___x_8180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8182_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_eqTrue_8041_ == 0 {
                    v___x_8163_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg(
                        v_a_8042_, v_a_8043_, v_a_8049_, v_a_8050_, v_a_8051_, v_a_8052_,
                    );
                    if lean_obj_tag(v___x_8163_) == 0 {
                        v_a_8164_ = lean_ctor_get(v___x_8163_, 0);
                        lean_inc(v_a_8164_);
                        lean_dec_ref_known(v___x_8163_, 1);
                        v_____x_8098_ = v_a_8164_;
                        v___y_8099_ = v_a_8042_;
                        v___y_8100_ = v_a_8043_;
                        v___y_8101_ = v_a_8044_;
                        v___y_8102_ = v_a_8045_;
                        v___y_8103_ = v_a_8046_;
                        v___y_8104_ = v_a_8047_;
                        v___y_8105_ = v_a_8048_;
                        v___y_8106_ = v_a_8049_;
                        v___y_8107_ = v_a_8050_;
                        v___y_8108_ = v_a_8051_;
                        v___y_8109_ = v_a_8052_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec_ref(v_e_8040_);
                        v_a_8165_ = lean_ctor_get(v___x_8163_, 0);
                        v_isSharedCheck_8172_ = (!lean_is_exclusive(v___x_8163_)) as u8;
                        if v_isSharedCheck_8172_ == 0 {
                            v___x_8167_ = v___x_8163_;
                            v_isShared_8168_ = v_isSharedCheck_8172_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_8165_);
                            lean_dec(v___x_8163_);
                            v___x_8167_ = lean_box(0);
                            v_isShared_8168_ = v_isSharedCheck_8172_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    v___x_8173_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg(
                        v_a_8042_, v_a_8043_, v_a_8049_, v_a_8050_, v_a_8051_, v_a_8052_,
                    );
                    if lean_obj_tag(v___x_8173_) == 0 {
                        v_a_8174_ = lean_ctor_get(v___x_8173_, 0);
                        lean_inc(v_a_8174_);
                        lean_dec_ref_known(v___x_8173_, 1);
                        v_____x_8098_ = v_a_8174_;
                        v___y_8099_ = v_a_8042_;
                        v___y_8100_ = v_a_8043_;
                        v___y_8101_ = v_a_8044_;
                        v___y_8102_ = v_a_8045_;
                        v___y_8103_ = v_a_8046_;
                        v___y_8104_ = v_a_8047_;
                        v___y_8105_ = v_a_8048_;
                        v___y_8106_ = v_a_8049_;
                        v___y_8107_ = v_a_8050_;
                        v___y_8108_ = v_a_8051_;
                        v___y_8109_ = v_a_8052_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec_ref(v_e_8040_);
                        v_a_8175_ = lean_ctor_get(v___x_8173_, 0);
                        v_isSharedCheck_8182_ = (!lean_is_exclusive(v___x_8173_)) as u8;
                        if v_isSharedCheck_8182_ == 0 {
                            v___x_8177_ = v___x_8173_;
                            v_isShared_8178_ = v_isSharedCheck_8182_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_8175_);
                            lean_dec(v___x_8173_);
                            v___x_8177_ = lean_box(0);
                            v_isShared_8178_ = v_isSharedCheck_8182_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_8055_ = lean_box(0);
                v___x_8056_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8056_, 0, v___x_8055_);
                return v___x_8056_;
            }
            2 => {
                lean_inc(v___y_8062_);
                v___x_8072_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(
                    v_fst_8070_,
                    v___y_8062_,
                    v___y_8068_,
                    v___y_8063_,
                    v___y_8060_,
                    v___y_8065_,
                    v___y_8058_,
                    v___y_8066_,
                    v___y_8059_,
                    v___y_8064_,
                    v___y_8061_,
                    v___y_8069_,
                );
                if lean_obj_tag(v___x_8072_) == 0 {
                    v_a_8073_ = lean_ctor_get(v___x_8072_, 0);
                    lean_inc(v_a_8073_);
                    lean_dec_ref_known(v___x_8072_, 1);
                    v___x_8074_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(
                        v_snd_8071_,
                        v___y_8062_,
                        v___y_8068_,
                        v___y_8063_,
                        v___y_8060_,
                        v___y_8065_,
                        v___y_8058_,
                        v___y_8066_,
                        v___y_8059_,
                        v___y_8064_,
                        v___y_8061_,
                        v___y_8069_,
                    );
                    if lean_obj_tag(v___x_8074_) == 0 {
                        v_a_8075_ = lean_ctor_get(v___x_8074_, 0);
                        lean_inc_n(v_a_8075_, 2);
                        lean_dec_ref_known(v___x_8074_, 1);
                        lean_inc(v_a_8073_);
                        v___x_8076_ = lean_alloc_ctor(3, 2, (0) as u32);
                        lean_ctor_set(v___x_8076_, 0, v_a_8073_);
                        lean_ctor_set(v___x_8076_, 1, v_a_8075_);
                        v___x_8077_ = l_Int_Linear_Expr_norm(v___x_8076_);
                        lean_dec_ref_known(v___x_8076_, 2);
                        v___x_8078_ = lean_alloc_ctor(2, 4, (1) as u32);
                        lean_ctor_set(v___x_8078_, 0, v_e_8040_);
                        lean_ctor_set(v___x_8078_, 1, v___y_8067_);
                        lean_ctor_set(v___x_8078_, 2, v_a_8073_);
                        lean_ctor_set(v___x_8078_, 3, v_a_8075_);
                        lean_ctor_set_uint8(
                            v___x_8078_,
                            (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                            v_eqTrue_8041_,
                        );
                        v___x_8079_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_8079_, 0, v___x_8077_);
                        lean_ctor_set(v___x_8079_, 1, v___x_8078_);
                        v___x_8080_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_8079_, v___y_8068_, v___y_8063_, v___y_8060_, v___y_8065_, v___y_8058_, v___y_8066_, v___y_8059_, v___y_8064_, v___y_8061_, v___y_8069_);
                        return v___x_8080_;
                    } else {
                        lean_dec(v_a_8073_);
                        lean_dec_ref(v___y_8067_);
                        lean_dec_ref(v_e_8040_);
                        v_a_8081_ = lean_ctor_get(v___x_8074_, 0);
                        v_isSharedCheck_8088_ = (!lean_is_exclusive(v___x_8074_)) as u8;
                        if v_isSharedCheck_8088_ == 0 {
                            v___x_8083_ = v___x_8074_;
                            v_isShared_8084_ = v_isSharedCheck_8088_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_8081_);
                            lean_dec(v___x_8074_);
                            v___x_8083_ = lean_box(0);
                            v_isShared_8084_ = v_isSharedCheck_8088_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_snd_8071_);
                    lean_dec_ref(v___y_8067_);
                    lean_dec(v___y_8062_);
                    lean_dec_ref(v_e_8040_);
                    v_a_8089_ = lean_ctor_get(v___x_8072_, 0);
                    v_isSharedCheck_8096_ = (!lean_is_exclusive(v___x_8072_)) as u8;
                    if v_isSharedCheck_8096_ == 0 {
                        v___x_8091_ = v___x_8072_;
                        v_isShared_8092_ = v_isSharedCheck_8096_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_8089_);
                        lean_dec(v___x_8072_);
                        v___x_8091_ = lean_box(0);
                        v_isShared_8092_ = v_isSharedCheck_8096_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_8084_ == 0 {
                    v___x_8086_ = v___x_8083_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8087_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8087_, 0, v_a_8081_);
                    v___x_8086_ = v_reuseFailAlloc_8087_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8086_;
            }
            5 => {
                if v_isShared_8092_ == 0 {
                    v___x_8094_ = v___x_8091_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8095_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8095_, 0, v_a_8089_);
                    v___x_8094_ = v_reuseFailAlloc_8095_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8094_;
            }
            7 => {
                if lean_obj_tag(v_____x_8098_) == 1 {
                    v_val_8110_ = lean_ctor_get(v_____x_8098_, 0);
                    lean_inc(v_val_8110_);
                    lean_dec_ref_known(v_____x_8098_, 1);
                    lean_inc_ref(v_e_8040_);
                    v___x_8111_ = l_Lean_Expr_cleanupAnnotations(v_e_8040_);
                    v___x_8112_ = l_Lean_Expr_isApp(v___x_8111_);
                    if v___x_8112_ == 0 {
                        lean_dec_ref(v___x_8111_);
                        lean_dec(v_val_8110_);
                        lean_dec_ref(v_e_8040_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_8113_ = lean_ctor_get(v___x_8111_, 1);
                        lean_inc_ref(v_arg_8113_);
                        v___x_8114_ = l_Lean_Expr_appFnCleanup___redArg(v___x_8111_);
                        v___x_8115_ = l_Lean_Expr_isApp(v___x_8114_);
                        if v___x_8115_ == 0 {
                            lean_dec_ref(v___x_8114_);
                            lean_dec_ref(v_arg_8113_);
                            lean_dec(v_val_8110_);
                            lean_dec_ref(v_e_8040_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_8116_ = lean_ctor_get(v___x_8114_, 1);
                            lean_inc_ref(v_arg_8116_);
                            v___x_8117_ = l_Lean_Expr_appFnCleanup___redArg(v___x_8114_);
                            v___x_8118_ = l_Lean_Expr_isApp(v___x_8117_);
                            if v___x_8118_ == 0 {
                                lean_dec_ref(v___x_8117_);
                                lean_dec_ref(v_arg_8116_);
                                lean_dec_ref(v_arg_8113_);
                                lean_dec(v_val_8110_);
                                lean_dec_ref(v_e_8040_);
                                state = 1;
                                continue;
                            } else {
                                v___x_8119_ = l_Lean_Expr_appFnCleanup___redArg(v___x_8117_);
                                v___x_8120_ = l_Lean_Expr_isApp(v___x_8119_);
                                if v___x_8120_ == 0 {
                                    lean_dec_ref(v___x_8119_);
                                    lean_dec_ref(v_arg_8116_);
                                    lean_dec_ref(v_arg_8113_);
                                    lean_dec(v_val_8110_);
                                    lean_dec_ref(v_e_8040_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_8121_ = l_Lean_Expr_appFnCleanup___redArg(v___x_8119_);
                                    v___x_8122_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2;
                                    v___x_8123_ = l_Lean_Expr_isConstOf(v___x_8121_, v___x_8122_);
                                    lean_dec_ref(v___x_8121_);
                                    if v___x_8123_ == 0 {
                                        lean_dec_ref(v_arg_8116_);
                                        lean_dec_ref(v_arg_8113_);
                                        lean_dec(v_val_8110_);
                                        lean_dec_ref(v_e_8040_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_8124_ = l_Lean_Meta_Grind_getGeneration___redArg(
                                            v_e_8040_,
                                            v___y_8100_,
                                        );
                                        if lean_obj_tag(v___x_8124_) == 0 {
                                            v_a_8125_ = lean_ctor_get(v___x_8124_, 0);
                                            lean_inc(v_a_8125_);
                                            lean_dec_ref_known(v___x_8124_, 1);
                                            lean_inc_ref(v_arg_8116_);
                                            v___x_8126_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(
                                                v_arg_8116_,
                                                v___y_8099_,
                                                v___y_8100_,
                                                v___y_8101_,
                                                v___y_8102_,
                                                v___y_8103_,
                                                v___y_8104_,
                                                v___y_8105_,
                                                v___y_8106_,
                                                v___y_8107_,
                                                v___y_8108_,
                                                v___y_8109_,
                                            );
                                            if lean_obj_tag(v___x_8126_) == 0 {
                                                v_a_8127_ = lean_ctor_get(v___x_8126_, 0);
                                                lean_inc(v_a_8127_);
                                                lean_dec_ref_known(v___x_8126_, 1);
                                                v_fst_8128_ = lean_ctor_get(v_a_8127_, 0);
                                                lean_inc(v_fst_8128_);
                                                v_snd_8129_ = lean_ctor_get(v_a_8127_, 1);
                                                lean_inc(v_snd_8129_);
                                                lean_dec(v_a_8127_);
                                                lean_inc_ref(v_arg_8113_);
                                                v___x_8130_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(
                                                    v_arg_8113_,
                                                    v___y_8099_,
                                                    v___y_8100_,
                                                    v___y_8101_,
                                                    v___y_8102_,
                                                    v___y_8103_,
                                                    v___y_8104_,
                                                    v___y_8105_,
                                                    v___y_8106_,
                                                    v___y_8107_,
                                                    v___y_8108_,
                                                    v___y_8109_,
                                                );
                                                if lean_obj_tag(v___x_8130_) == 0 {
                                                    v_a_8131_ = lean_ctor_get(v___x_8130_, 0);
                                                    lean_inc(v_a_8131_);
                                                    lean_dec_ref_known(v___x_8130_, 1);
                                                    v_fst_8132_ = lean_ctor_get(v_a_8131_, 0);
                                                    lean_inc_n(v_fst_8132_, 2);
                                                    v_snd_8133_ = lean_ctor_get(v_a_8131_, 1);
                                                    lean_inc(v_snd_8133_);
                                                    lean_dec(v_a_8131_);
                                                    lean_inc(v_fst_8128_);
                                                    v___x_8134_ = l_Lean_mkApp6(
                                                        v_val_8110_,
                                                        v_arg_8116_,
                                                        v_arg_8113_,
                                                        v_fst_8128_,
                                                        v_fst_8132_,
                                                        v_snd_8129_,
                                                        v_snd_8133_,
                                                    );
                                                    if v_eqTrue_8041_ == 0 {
                                                        v___x_8135_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
                                                        v___x_8136_ = l_Lean_mkIntAdd(
                                                            v_fst_8132_,
                                                            v___x_8135_,
                                                        );
                                                        v___y_8058_ = v___y_8104_;
                                                        v___y_8059_ = v___y_8106_;
                                                        v___y_8060_ = v___y_8102_;
                                                        v___y_8061_ = v___y_8108_;
                                                        v___y_8062_ = v_a_8125_;
                                                        v___y_8063_ = v___y_8101_;
                                                        v___y_8064_ = v___y_8107_;
                                                        v___y_8065_ = v___y_8103_;
                                                        v___y_8066_ = v___y_8105_;
                                                        v___y_8067_ = v___x_8134_;
                                                        v___y_8068_ = v___y_8100_;
                                                        v___y_8069_ = v___y_8109_;
                                                        v_fst_8070_ = v___x_8136_;
                                                        v_snd_8071_ = v_fst_8128_;
                                                        state = 2;
                                                        continue;
                                                    } else {
                                                        v___y_8058_ = v___y_8104_;
                                                        v___y_8059_ = v___y_8106_;
                                                        v___y_8060_ = v___y_8102_;
                                                        v___y_8061_ = v___y_8108_;
                                                        v___y_8062_ = v_a_8125_;
                                                        v___y_8063_ = v___y_8101_;
                                                        v___y_8064_ = v___y_8107_;
                                                        v___y_8065_ = v___y_8103_;
                                                        v___y_8066_ = v___y_8105_;
                                                        v___y_8067_ = v___x_8134_;
                                                        v___y_8068_ = v___y_8100_;
                                                        v___y_8069_ = v___y_8109_;
                                                        v_fst_8070_ = v_fst_8128_;
                                                        v_snd_8071_ = v_fst_8132_;
                                                        state = 2;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec(v_snd_8129_);
                                                    lean_dec(v_fst_8128_);
                                                    lean_dec(v_a_8125_);
                                                    lean_dec_ref(v_arg_8116_);
                                                    lean_dec_ref(v_arg_8113_);
                                                    lean_dec(v_val_8110_);
                                                    lean_dec_ref(v_e_8040_);
                                                    v_a_8137_ = lean_ctor_get(v___x_8130_, 0);
                                                    v_isSharedCheck_8144_ =
                                                        (!lean_is_exclusive(v___x_8130_)) as u8;
                                                    if v_isSharedCheck_8144_ == 0 {
                                                        v___x_8139_ = v___x_8130_;
                                                        v_isShared_8140_ = v_isSharedCheck_8144_;
                                                        state = 8;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_8137_);
                                                        lean_dec(v___x_8130_);
                                                        v___x_8139_ = lean_box(0);
                                                        v_isShared_8140_ = v_isSharedCheck_8144_;
                                                        state = 8;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                lean_dec(v_a_8125_);
                                                lean_dec_ref(v_arg_8116_);
                                                lean_dec_ref(v_arg_8113_);
                                                lean_dec(v_val_8110_);
                                                lean_dec_ref(v_e_8040_);
                                                v_a_8145_ = lean_ctor_get(v___x_8126_, 0);
                                                v_isSharedCheck_8152_ =
                                                    (!lean_is_exclusive(v___x_8126_)) as u8;
                                                if v_isSharedCheck_8152_ == 0 {
                                                    v___x_8147_ = v___x_8126_;
                                                    v_isShared_8148_ = v_isSharedCheck_8152_;
                                                    state = 10;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_8145_);
                                                    lean_dec(v___x_8126_);
                                                    v___x_8147_ = lean_box(0);
                                                    v_isShared_8148_ = v_isSharedCheck_8152_;
                                                    state = 10;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v_arg_8116_);
                                            lean_dec_ref(v_arg_8113_);
                                            lean_dec(v_val_8110_);
                                            lean_dec_ref(v_e_8040_);
                                            v_a_8153_ = lean_ctor_get(v___x_8124_, 0);
                                            v_isSharedCheck_8160_ =
                                                (!lean_is_exclusive(v___x_8124_)) as u8;
                                            if v_isSharedCheck_8160_ == 0 {
                                                v___x_8155_ = v___x_8124_;
                                                v_isShared_8156_ = v_isSharedCheck_8160_;
                                                state = 12;
                                                continue;
                                            } else {
                                                lean_inc(v_a_8153_);
                                                lean_dec(v___x_8124_);
                                                v___x_8155_ = lean_box(0);
                                                v_isShared_8156_ = v_isSharedCheck_8160_;
                                                state = 12;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    lean_dec(v_____x_8098_);
                    lean_dec_ref(v_e_8040_);
                    v___x_8161_ = lean_box(0);
                    v___x_8162_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8162_, 0, v___x_8161_);
                    return v___x_8162_;
                }
            }
            8 => {
                if v_isShared_8140_ == 0 {
                    v___x_8142_ = v___x_8139_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8143_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8143_, 0, v_a_8137_);
                    v___x_8142_ = v_reuseFailAlloc_8143_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8142_;
            }
            10 => {
                if v_isShared_8148_ == 0 {
                    v___x_8150_ = v___x_8147_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_8151_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8151_, 0, v_a_8145_);
                    v___x_8150_ = v_reuseFailAlloc_8151_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_8150_;
            }
            12 => {
                if v_isShared_8156_ == 0 {
                    v___x_8158_ = v___x_8155_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_8159_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8159_, 0, v_a_8153_);
                    v___x_8158_ = v_reuseFailAlloc_8159_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_8158_;
            }
            14 => {
                if v_isShared_8168_ == 0 {
                    v___x_8170_ = v___x_8167_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_8171_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8171_, 0, v_a_8165_);
                    v___x_8170_ = v_reuseFailAlloc_8171_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_8170_;
            }
            16 => {
                if v_isShared_8178_ == 0 {
                    v___x_8180_ = v___x_8177_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_8181_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8181_, 0, v_a_8175_);
                    v___x_8180_ = v_reuseFailAlloc_8181_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_8180_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed(
    mut v_e_8183_: *mut LeanObject,
    mut v_eqTrue_8184_: *mut LeanObject,
    mut v_a_8185_: *mut LeanObject,
    mut v_a_8186_: *mut LeanObject,
    mut v_a_8187_: *mut LeanObject,
    mut v_a_8188_: *mut LeanObject,
    mut v_a_8189_: *mut LeanObject,
    mut v_a_8190_: *mut LeanObject,
    mut v_a_8191_: *mut LeanObject,
    mut v_a_8192_: *mut LeanObject,
    mut v_a_8193_: *mut LeanObject,
    mut v_a_8194_: *mut LeanObject,
    mut v_a_8195_: *mut LeanObject,
    mut v_a_8196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eqTrue_boxed_8197_: u8 = 0;
    let mut v_res_8198_: *mut LeanObject = core::ptr::null_mut();
    v_eqTrue_boxed_8197_ = (lean_unbox(v_eqTrue_8184_) as u8);
    v_res_8198_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(
        v_e_8183_,
        v_eqTrue_boxed_8197_,
        v_a_8185_,
        v_a_8186_,
        v_a_8187_,
        v_a_8188_,
        v_a_8189_,
        v_a_8190_,
        v_a_8191_,
        v_a_8192_,
        v_a_8193_,
        v_a_8194_,
        v_a_8195_,
    );
    lean_dec(v_a_8195_);
    lean_dec_ref(v_a_8194_);
    lean_dec(v_a_8193_);
    lean_dec_ref(v_a_8192_);
    lean_dec(v_a_8191_);
    lean_dec_ref(v_a_8190_);
    lean_dec(v_a_8189_);
    lean_dec_ref(v_a_8188_);
    lean_dec(v_a_8187_);
    lean_dec(v_a_8186_);
    lean_dec(v_a_8185_);
    return v_res_8198_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(
    mut v_e_8204_: *mut LeanObject,
    mut v_eqTrue_8205_: u8,
    mut v_a_8206_: *mut LeanObject,
    mut v_a_8207_: *mut LeanObject,
    mut v_a_8208_: *mut LeanObject,
    mut v_a_8209_: *mut LeanObject,
    mut v_a_8210_: *mut LeanObject,
    mut v_a_8211_: *mut LeanObject,
    mut v_a_8212_: *mut LeanObject,
    mut v_a_8213_: *mut LeanObject,
    mut v_a_8214_: *mut LeanObject,
    mut v_a_8215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8224_: u8 = 0;
    let mut v_lia_8225_: u8 = 0;
    let mut v___x_8226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8231_: u8 = 0;
    let mut v___x_8232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8233_: u8 = 0;
    let mut v___x_8234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8235_: u8 = 0;
    let mut v___x_8236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8237_: u8 = 0;
    let mut v_arg_8238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8241_: u8 = 0;
    let mut v___x_8242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8243_: u8 = 0;
    let mut v___x_8244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8245_: u8 = 0;
    let mut v___x_8246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8251_: u8 = 0;
    let mut v_a_8252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8255_: u8 = 0;
    let mut v___x_8257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8259_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8220_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_8208_);
                if lean_obj_tag(v___x_8220_) == 0 {
                    v_a_8221_ = lean_ctor_get(v___x_8220_, 0);
                    v_isSharedCheck_8251_ = (!lean_is_exclusive(v___x_8220_)) as u8;
                    if v_isSharedCheck_8251_ == 0 {
                        v___x_8223_ = v___x_8220_;
                        v_isShared_8224_ = v_isSharedCheck_8251_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_8221_);
                        lean_dec(v___x_8220_);
                        v___x_8223_ = lean_box(0);
                        v_isShared_8224_ = v_isSharedCheck_8251_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_8204_);
                    v_a_8252_ = lean_ctor_get(v___x_8220_, 0);
                    v_isSharedCheck_8259_ = (!lean_is_exclusive(v___x_8220_)) as u8;
                    if v_isSharedCheck_8259_ == 0 {
                        v___x_8254_ = v___x_8220_;
                        v_isShared_8255_ = v_isSharedCheck_8259_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_8252_);
                        lean_dec(v___x_8220_);
                        v___x_8254_ = lean_box(0);
                        v_isShared_8255_ = v_isSharedCheck_8259_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8218_ = lean_box(0);
                v___x_8219_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8219_, 0, v___x_8218_);
                return v___x_8219_;
            }
            2 => {
                v_lia_8225_ = lean_ctor_get_uint8(
                    v_a_8221_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 23) as u32,
                );
                lean_dec(v_a_8221_);
                if v_lia_8225_ == 0 {
                    lean_dec_ref(v_e_8204_);
                    v___x_8226_ = lean_box(0);
                    if v_isShared_8224_ == 0 {
                        lean_ctor_set(v___x_8223_, 0, v___x_8226_);
                        v___x_8228_ = v___x_8223_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8229_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8229_, 0, v___x_8226_);
                        v___x_8228_ = v_reuseFailAlloc_8229_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8223_);
                    lean_inc_ref(v_e_8204_);
                    v___x_8230_ = l_Lean_Expr_cleanupAnnotations(v_e_8204_);
                    v___x_8231_ = l_Lean_Expr_isApp(v___x_8230_);
                    if v___x_8231_ == 0 {
                        lean_dec_ref(v___x_8230_);
                        lean_dec_ref(v_e_8204_);
                        state = 1;
                        continue;
                    } else {
                        v___x_8232_ = l_Lean_Expr_appFnCleanup___redArg(v___x_8230_);
                        v___x_8233_ = l_Lean_Expr_isApp(v___x_8232_);
                        if v___x_8233_ == 0 {
                            lean_dec_ref(v___x_8232_);
                            lean_dec_ref(v_e_8204_);
                            state = 1;
                            continue;
                        } else {
                            v___x_8234_ = l_Lean_Expr_appFnCleanup___redArg(v___x_8232_);
                            v___x_8235_ = l_Lean_Expr_isApp(v___x_8234_);
                            if v___x_8235_ == 0 {
                                lean_dec_ref(v___x_8234_);
                                lean_dec_ref(v_e_8204_);
                                state = 1;
                                continue;
                            } else {
                                v___x_8236_ = l_Lean_Expr_appFnCleanup___redArg(v___x_8234_);
                                v___x_8237_ = l_Lean_Expr_isApp(v___x_8236_);
                                if v___x_8237_ == 0 {
                                    lean_dec_ref(v___x_8236_);
                                    lean_dec_ref(v_e_8204_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_8238_ = lean_ctor_get(v___x_8236_, 1);
                                    lean_inc_ref(v_arg_8238_);
                                    v___x_8239_ = l_Lean_Expr_appFnCleanup___redArg(v___x_8236_);
                                    v___x_8240_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2;
                                    v___x_8241_ = l_Lean_Expr_isConstOf(v___x_8239_, v___x_8240_);
                                    lean_dec_ref(v___x_8239_);
                                    if v___x_8241_ == 0 {
                                        lean_dec_ref(v_arg_8238_);
                                        lean_dec_ref(v_e_8204_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_8242_ =
                                            l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0;
                                        v___x_8243_ =
                                            l_Lean_Expr_isConstOf(v_arg_8238_, v___x_8242_);
                                        if v___x_8243_ == 0 {
                                            v___x_8244_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2;
                                            v___x_8245_ =
                                                l_Lean_Expr_isConstOf(v_arg_8238_, v___x_8244_);
                                            if v___x_8245_ == 0 {
                                                v___x_8246_ = lean_box((v_eqTrue_8205_) as usize);
                                                v___x_8247_ = lean_alloc_closure(l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed as *mut core::ffi::c_void, 14, 2);
                                                lean_closure_set(v___x_8247_, 0, v_e_8204_);
                                                lean_closure_set(v___x_8247_, 1, v___x_8246_);
                                                v___x_8248_ =
                                                    l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(
                                                        v_arg_8238_,
                                                        v___x_8247_,
                                                        v_a_8206_,
                                                        v_a_8207_,
                                                        v_a_8208_,
                                                        v_a_8209_,
                                                        v_a_8210_,
                                                        v_a_8211_,
                                                        v_a_8212_,
                                                        v_a_8213_,
                                                        v_a_8214_,
                                                        v_a_8215_,
                                                    );
                                                return v___x_8248_;
                                            } else {
                                                lean_dec_ref(v_arg_8238_);
                                                v___x_8249_ =
                                                    l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(
                                                        v_e_8204_,
                                                        v_eqTrue_8205_,
                                                        v_a_8206_,
                                                        v_a_8207_,
                                                        v_a_8208_,
                                                        v_a_8209_,
                                                        v_a_8210_,
                                                        v_a_8211_,
                                                        v_a_8212_,
                                                        v_a_8213_,
                                                        v_a_8214_,
                                                        v_a_8215_,
                                                    );
                                                return v___x_8249_;
                                            }
                                        } else {
                                            lean_dec_ref(v_arg_8238_);
                                            v___x_8250_ =
                                                l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(
                                                    v_e_8204_,
                                                    v_eqTrue_8205_,
                                                    v_a_8206_,
                                                    v_a_8207_,
                                                    v_a_8208_,
                                                    v_a_8209_,
                                                    v_a_8210_,
                                                    v_a_8211_,
                                                    v_a_8212_,
                                                    v_a_8213_,
                                                    v_a_8214_,
                                                    v_a_8215_,
                                                );
                                            return v___x_8250_;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                return v___x_8228_;
            }
            4 => {
                if v_isShared_8255_ == 0 {
                    v___x_8257_ = v___x_8254_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8258_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8258_, 0, v_a_8252_);
                    v___x_8257_ = v_reuseFailAlloc_8258_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8257_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___boxed(
    mut v_e_8260_: *mut LeanObject,
    mut v_eqTrue_8261_: *mut LeanObject,
    mut v_a_8262_: *mut LeanObject,
    mut v_a_8263_: *mut LeanObject,
    mut v_a_8264_: *mut LeanObject,
    mut v_a_8265_: *mut LeanObject,
    mut v_a_8266_: *mut LeanObject,
    mut v_a_8267_: *mut LeanObject,
    mut v_a_8268_: *mut LeanObject,
    mut v_a_8269_: *mut LeanObject,
    mut v_a_8270_: *mut LeanObject,
    mut v_a_8271_: *mut LeanObject,
    mut v_a_8272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eqTrue_boxed_8273_: u8 = 0;
    let mut v_res_8274_: *mut LeanObject = core::ptr::null_mut();
    v_eqTrue_boxed_8273_ = (lean_unbox(v_eqTrue_8261_) as u8);
    v_res_8274_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(
        v_e_8260_,
        v_eqTrue_boxed_8273_,
        v_a_8262_,
        v_a_8263_,
        v_a_8264_,
        v_a_8265_,
        v_a_8266_,
        v_a_8267_,
        v_a_8268_,
        v_a_8269_,
        v_a_8270_,
        v_a_8271_,
    );
    lean_dec(v_a_8271_);
    lean_dec_ref(v_a_8270_);
    lean_dec(v_a_8269_);
    lean_dec_ref(v_a_8268_);
    lean_dec(v_a_8267_);
    lean_dec_ref(v_a_8266_);
    lean_dec(v_a_8265_);
    lean_dec_ref(v_a_8264_);
    lean_dec(v_a_8263_);
    lean_dec(v_a_8262_);
    return v_res_8274_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(
    mut v_e_8275_: *mut LeanObject,
    mut v_arg_8276_: *mut LeanObject,
    mut v_arg_8277_: *mut LeanObject,
    mut v_eqTrue_8278_: u8,
    mut v_____x_8279_: *mut LeanObject,
    mut v___y_8280_: *mut LeanObject,
    mut v___y_8281_: *mut LeanObject,
    mut v___y_8282_: *mut LeanObject,
    mut v___y_8283_: *mut LeanObject,
    mut v___y_8284_: *mut LeanObject,
    mut v___y_8285_: *mut LeanObject,
    mut v___y_8286_: *mut LeanObject,
    mut v___y_8287_: *mut LeanObject,
    mut v___y_8288_: *mut LeanObject,
    mut v___y_8289_: *mut LeanObject,
    mut v___y_8290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_8292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8301_: u8 = 0;
    let mut v___x_8302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8308_: u8 = 0;
    let mut v___x_8309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8329_: u8 = 0;
    let mut v___x_8331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8333_: u8 = 0;
    let mut v_a_8334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8337_: u8 = 0;
    let mut v___x_8339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8341_: u8 = 0;
    let mut v___x_8342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8344_: u8 = 0;
    let mut v_a_8345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8348_: u8 = 0;
    let mut v___x_8350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8352_: u8 = 0;
    let mut v_isSharedCheck_8353_: u8 = 0;
    let mut v_a_8354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8357_: u8 = 0;
    let mut v___x_8359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8361_: u8 = 0;
    let mut v_a_8362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8365_: u8 = 0;
    let mut v___x_8367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8369_: u8 = 0;
    let mut v___x_8370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8371_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____x_8279_) == 1 {
                    v_val_8292_ = lean_ctor_get(v_____x_8279_, 0);
                    lean_inc(v_val_8292_);
                    lean_dec_ref_known(v_____x_8279_, 1);
                    v___x_8293_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_8275_, v___y_8281_);
                    if lean_obj_tag(v___x_8293_) == 0 {
                        v_a_8294_ = lean_ctor_get(v___x_8293_, 0);
                        lean_inc(v_a_8294_);
                        lean_dec_ref_known(v___x_8293_, 1);
                        lean_inc_ref(v_arg_8276_);
                        v___x_8295_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(
                            v_arg_8276_,
                            v___y_8280_,
                            v___y_8281_,
                            v___y_8282_,
                            v___y_8283_,
                            v___y_8284_,
                            v___y_8285_,
                            v___y_8286_,
                            v___y_8287_,
                            v___y_8288_,
                            v___y_8289_,
                            v___y_8290_,
                        );
                        if lean_obj_tag(v___x_8295_) == 0 {
                            v_a_8296_ = lean_ctor_get(v___x_8295_, 0);
                            lean_inc(v_a_8296_);
                            lean_dec_ref_known(v___x_8295_, 1);
                            v_fst_8297_ = lean_ctor_get(v_a_8296_, 0);
                            v_snd_8298_ = lean_ctor_get(v_a_8296_, 1);
                            v_isSharedCheck_8353_ = (!lean_is_exclusive(v_a_8296_)) as u8;
                            if v_isSharedCheck_8353_ == 0 {
                                v___x_8300_ = v_a_8296_;
                                v_isShared_8301_ = v_isSharedCheck_8353_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_snd_8298_);
                                lean_inc(v_fst_8297_);
                                lean_dec(v_a_8296_);
                                v___x_8300_ = lean_box(0);
                                v_isShared_8301_ = v_isSharedCheck_8353_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_8294_);
                            lean_dec(v_val_8292_);
                            lean_dec_ref(v_arg_8277_);
                            lean_dec_ref(v_arg_8276_);
                            lean_dec_ref(v_e_8275_);
                            v_a_8354_ = lean_ctor_get(v___x_8295_, 0);
                            v_isSharedCheck_8361_ = (!lean_is_exclusive(v___x_8295_)) as u8;
                            if v_isSharedCheck_8361_ == 0 {
                                v___x_8356_ = v___x_8295_;
                                v_isShared_8357_ = v_isSharedCheck_8361_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_8354_);
                                lean_dec(v___x_8295_);
                                v___x_8356_ = lean_box(0);
                                v_isShared_8357_ = v_isSharedCheck_8361_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_8292_);
                        lean_dec_ref(v_arg_8277_);
                        lean_dec_ref(v_arg_8276_);
                        lean_dec_ref(v_e_8275_);
                        v_a_8362_ = lean_ctor_get(v___x_8293_, 0);
                        v_isSharedCheck_8369_ = (!lean_is_exclusive(v___x_8293_)) as u8;
                        if v_isSharedCheck_8369_ == 0 {
                            v___x_8364_ = v___x_8293_;
                            v_isShared_8365_ = v_isSharedCheck_8369_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_8362_);
                            lean_dec(v___x_8293_);
                            v___x_8364_ = lean_box(0);
                            v_isShared_8365_ = v_isSharedCheck_8369_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_____x_8279_);
                    lean_dec_ref(v_arg_8277_);
                    lean_dec_ref(v_arg_8276_);
                    lean_dec_ref(v_e_8275_);
                    v___x_8370_ = lean_box(0);
                    v___x_8371_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8371_, 0, v___x_8370_);
                    return v___x_8371_;
                }
            }
            1 => {
                lean_inc_ref(v_arg_8277_);
                v___x_8302_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(
                    v_arg_8277_,
                    v___y_8280_,
                    v___y_8281_,
                    v___y_8282_,
                    v___y_8283_,
                    v___y_8284_,
                    v___y_8285_,
                    v___y_8286_,
                    v___y_8287_,
                    v___y_8288_,
                    v___y_8289_,
                    v___y_8290_,
                );
                if lean_obj_tag(v___x_8302_) == 0 {
                    v_a_8303_ = lean_ctor_get(v___x_8302_, 0);
                    lean_inc(v_a_8303_);
                    lean_dec_ref_known(v___x_8302_, 1);
                    v_fst_8304_ = lean_ctor_get(v_a_8303_, 0);
                    v_snd_8305_ = lean_ctor_get(v_a_8303_, 1);
                    v_isSharedCheck_8344_ = (!lean_is_exclusive(v_a_8303_)) as u8;
                    if v_isSharedCheck_8344_ == 0 {
                        v___x_8307_ = v_a_8303_;
                        v_isShared_8308_ = v_isSharedCheck_8344_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_8305_);
                        lean_inc(v_fst_8304_);
                        lean_dec(v_a_8303_);
                        v___x_8307_ = lean_box(0);
                        v_isShared_8308_ = v_isSharedCheck_8344_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8300_);
                    lean_dec(v_snd_8298_);
                    lean_dec(v_fst_8297_);
                    lean_dec(v_a_8294_);
                    lean_dec(v_val_8292_);
                    lean_dec_ref(v_arg_8277_);
                    lean_dec_ref(v_arg_8276_);
                    lean_dec_ref(v_e_8275_);
                    v_a_8345_ = lean_ctor_get(v___x_8302_, 0);
                    v_isSharedCheck_8352_ = (!lean_is_exclusive(v___x_8302_)) as u8;
                    if v_isSharedCheck_8352_ == 0 {
                        v___x_8347_ = v___x_8302_;
                        v_isShared_8348_ = v_isSharedCheck_8352_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_8345_);
                        lean_dec(v___x_8302_);
                        v___x_8347_ = lean_box(0);
                        v_isShared_8348_ = v_isSharedCheck_8352_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                lean_inc(v_fst_8304_);
                lean_inc(v_fst_8297_);
                v___x_8309_ = l_Lean_mkApp6(
                    v_val_8292_,
                    v_arg_8276_,
                    v_arg_8277_,
                    v_fst_8297_,
                    v_fst_8304_,
                    v_snd_8298_,
                    v_snd_8305_,
                );
                if v_eqTrue_8278_ == 0 {
                    v_fst_8311_ = v_fst_8304_;
                    v_snd_8312_ = v_fst_8297_;
                    state = 3;
                    continue;
                } else {
                    v___x_8342_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0,
                    );
                    v___x_8343_ = l_Lean_mkIntAdd(v_fst_8297_, v___x_8342_);
                    v_fst_8311_ = v___x_8343_;
                    v_snd_8312_ = v_fst_8304_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc(v_a_8294_);
                v___x_8313_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(
                    v_fst_8311_,
                    v_a_8294_,
                    v___y_8281_,
                    v___y_8282_,
                    v___y_8283_,
                    v___y_8284_,
                    v___y_8285_,
                    v___y_8286_,
                    v___y_8287_,
                    v___y_8288_,
                    v___y_8289_,
                    v___y_8290_,
                );
                if lean_obj_tag(v___x_8313_) == 0 {
                    v_a_8314_ = lean_ctor_get(v___x_8313_, 0);
                    lean_inc(v_a_8314_);
                    lean_dec_ref_known(v___x_8313_, 1);
                    v___x_8315_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(
                        v_snd_8312_,
                        v_a_8294_,
                        v___y_8281_,
                        v___y_8282_,
                        v___y_8283_,
                        v___y_8284_,
                        v___y_8285_,
                        v___y_8286_,
                        v___y_8287_,
                        v___y_8288_,
                        v___y_8289_,
                        v___y_8290_,
                    );
                    if lean_obj_tag(v___x_8315_) == 0 {
                        v_a_8316_ = lean_ctor_get(v___x_8315_, 0);
                        lean_inc_n(v_a_8316_, 2);
                        lean_dec_ref_known(v___x_8315_, 1);
                        lean_inc(v_a_8314_);
                        if v_isShared_8308_ == 0 {
                            lean_ctor_set_tag(v___x_8307_, 3);
                            lean_ctor_set(v___x_8307_, 1, v_a_8316_);
                            lean_ctor_set(v___x_8307_, 0, v_a_8314_);
                            v___x_8318_ = v___x_8307_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_8325_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_8325_, 0, v_a_8314_);
                            lean_ctor_set(v_reuseFailAlloc_8325_, 1, v_a_8316_);
                            v___x_8318_ = v_reuseFailAlloc_8325_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_8314_);
                        lean_dec_ref(v___x_8309_);
                        lean_del_object(v___x_8307_);
                        lean_del_object(v___x_8300_);
                        lean_dec_ref(v_e_8275_);
                        v_a_8326_ = lean_ctor_get(v___x_8315_, 0);
                        v_isSharedCheck_8333_ = (!lean_is_exclusive(v___x_8315_)) as u8;
                        if v_isSharedCheck_8333_ == 0 {
                            v___x_8328_ = v___x_8315_;
                            v_isShared_8329_ = v_isSharedCheck_8333_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_8326_);
                            lean_dec(v___x_8315_);
                            v___x_8328_ = lean_box(0);
                            v_isShared_8329_ = v_isSharedCheck_8333_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_snd_8312_);
                    lean_dec_ref(v___x_8309_);
                    lean_del_object(v___x_8307_);
                    lean_del_object(v___x_8300_);
                    lean_dec(v_a_8294_);
                    lean_dec_ref(v_e_8275_);
                    v_a_8334_ = lean_ctor_get(v___x_8313_, 0);
                    v_isSharedCheck_8341_ = (!lean_is_exclusive(v___x_8313_)) as u8;
                    if v_isSharedCheck_8341_ == 0 {
                        v___x_8336_ = v___x_8313_;
                        v_isShared_8337_ = v_isSharedCheck_8341_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_8334_);
                        lean_dec(v___x_8313_);
                        v___x_8336_ = lean_box(0);
                        v_isShared_8337_ = v_isSharedCheck_8341_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v___x_8319_ = l_Int_Linear_Expr_norm(v___x_8318_);
                lean_dec_ref(v___x_8318_);
                v___x_8320_ = lean_alloc_ctor(2, 4, (1) as u32);
                lean_ctor_set(v___x_8320_, 0, v_e_8275_);
                lean_ctor_set(v___x_8320_, 1, v___x_8309_);
                lean_ctor_set(v___x_8320_, 2, v_a_8314_);
                lean_ctor_set(v___x_8320_, 3, v_a_8316_);
                lean_ctor_set_uint8(
                    v___x_8320_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v_eqTrue_8278_,
                );
                if v_isShared_8301_ == 0 {
                    lean_ctor_set(v___x_8300_, 1, v___x_8320_);
                    lean_ctor_set(v___x_8300_, 0, v___x_8319_);
                    v___x_8322_ = v___x_8300_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8324_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8324_, 0, v___x_8319_);
                    lean_ctor_set(v_reuseFailAlloc_8324_, 1, v___x_8320_);
                    v___x_8322_ = v_reuseFailAlloc_8324_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc(v___y_8290_);
                lean_inc_ref(v___y_8289_);
                lean_inc(v___y_8288_);
                lean_inc_ref(v___y_8287_);
                lean_inc(v___y_8286_);
                lean_inc_ref(v___y_8285_);
                lean_inc(v___y_8284_);
                lean_inc_ref(v___y_8283_);
                lean_inc(v___y_8282_);
                lean_inc(v___y_8281_);
                v___x_8323_ = lean_grind_cutsat_assert_le(
                    v___x_8322_,
                    v___y_8281_,
                    v___y_8282_,
                    v___y_8283_,
                    v___y_8284_,
                    v___y_8285_,
                    v___y_8286_,
                    v___y_8287_,
                    v___y_8288_,
                    v___y_8289_,
                    v___y_8290_,
                );
                return v___x_8323_;
            }
            6 => {
                if v_isShared_8329_ == 0 {
                    v___x_8331_ = v___x_8328_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8332_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8332_, 0, v_a_8326_);
                    v___x_8331_ = v_reuseFailAlloc_8332_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8331_;
            }
            8 => {
                if v_isShared_8337_ == 0 {
                    v___x_8339_ = v___x_8336_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8340_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8340_, 0, v_a_8334_);
                    v___x_8339_ = v_reuseFailAlloc_8340_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8339_;
            }
            10 => {
                if v_isShared_8348_ == 0 {
                    v___x_8350_ = v___x_8347_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_8351_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8351_, 0, v_a_8345_);
                    v___x_8350_ = v_reuseFailAlloc_8351_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_8350_;
            }
            12 => {
                if v_isShared_8357_ == 0 {
                    v___x_8359_ = v___x_8356_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_8360_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8360_, 0, v_a_8354_);
                    v___x_8359_ = v_reuseFailAlloc_8360_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_8359_;
            }
            14 => {
                if v_isShared_8365_ == 0 {
                    v___x_8367_ = v___x_8364_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_8368_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8368_, 0, v_a_8362_);
                    v___x_8367_ = v_reuseFailAlloc_8368_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_8367_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_8372_: *mut LeanObject = *_args.add(0);
    let mut v_arg_8373_: *mut LeanObject = *_args.add(1);
    let mut v_arg_8374_: *mut LeanObject = *_args.add(2);
    let mut v_eqTrue_8375_: *mut LeanObject = *_args.add(3);
    let mut v_____x_8376_: *mut LeanObject = *_args.add(4);
    let mut v___y_8377_: *mut LeanObject = *_args.add(5);
    let mut v___y_8378_: *mut LeanObject = *_args.add(6);
    let mut v___y_8379_: *mut LeanObject = *_args.add(7);
    let mut v___y_8380_: *mut LeanObject = *_args.add(8);
    let mut v___y_8381_: *mut LeanObject = *_args.add(9);
    let mut v___y_8382_: *mut LeanObject = *_args.add(10);
    let mut v___y_8383_: *mut LeanObject = *_args.add(11);
    let mut v___y_8384_: *mut LeanObject = *_args.add(12);
    let mut v___y_8385_: *mut LeanObject = *_args.add(13);
    let mut v___y_8386_: *mut LeanObject = *_args.add(14);
    let mut v___y_8387_: *mut LeanObject = *_args.add(15);
    let mut v___y_8388_: *mut LeanObject = *_args.add(16);
    let mut v_eqTrue_boxed_8389_: u8 = 0;
    let mut v_res_8390_: *mut LeanObject = core::ptr::null_mut();
    v_eqTrue_boxed_8389_ = (lean_unbox(v_eqTrue_8375_) as u8);
    v_res_8390_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(
        v_e_8372_,
        v_arg_8373_,
        v_arg_8374_,
        v_eqTrue_boxed_8389_,
        v_____x_8376_,
        v___y_8377_,
        v___y_8378_,
        v___y_8379_,
        v___y_8380_,
        v___y_8381_,
        v___y_8382_,
        v___y_8383_,
        v___y_8384_,
        v___y_8385_,
        v___y_8386_,
        v___y_8387_,
    );
    lean_dec(v___y_8387_);
    lean_dec_ref(v___y_8386_);
    lean_dec(v___y_8385_);
    lean_dec_ref(v___y_8384_);
    lean_dec(v___y_8383_);
    lean_dec_ref(v___y_8382_);
    lean_dec(v___y_8381_);
    lean_dec_ref(v___y_8380_);
    lean_dec(v___y_8379_);
    lean_dec(v___y_8378_);
    lean_dec(v___y_8377_);
    return v_res_8390_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(
    mut v_eqTrue_8391_: u8,
    mut v___f_8392_: *mut LeanObject,
    mut v___y_8393_: *mut LeanObject,
    mut v___y_8394_: *mut LeanObject,
    mut v___y_8395_: *mut LeanObject,
    mut v___y_8396_: *mut LeanObject,
    mut v___y_8397_: *mut LeanObject,
    mut v___y_8398_: *mut LeanObject,
    mut v___y_8399_: *mut LeanObject,
    mut v___y_8400_: *mut LeanObject,
    mut v___y_8401_: *mut LeanObject,
    mut v___y_8402_: *mut LeanObject,
    mut v___y_8403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8411_: u8 = 0;
    let mut v___x_8413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8415_: u8 = 0;
    let mut v___x_8416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8422_: u8 = 0;
    let mut v___x_8424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_eqTrue_8391_ == 0 {
                    v___x_8405_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg(
                        v___y_8393_,
                        v___y_8394_,
                        v___y_8400_,
                        v___y_8401_,
                        v___y_8402_,
                        v___y_8403_,
                    );
                    if lean_obj_tag(v___x_8405_) == 0 {
                        v_a_8406_ = lean_ctor_get(v___x_8405_, 0);
                        lean_inc(v_a_8406_);
                        lean_dec_ref_known(v___x_8405_, 1);
                        lean_inc(v___y_8403_);
                        lean_inc_ref(v___y_8402_);
                        lean_inc(v___y_8401_);
                        lean_inc_ref(v___y_8400_);
                        lean_inc(v___y_8399_);
                        lean_inc_ref(v___y_8398_);
                        lean_inc(v___y_8397_);
                        lean_inc_ref(v___y_8396_);
                        lean_inc(v___y_8395_);
                        lean_inc(v___y_8394_);
                        lean_inc(v___y_8393_);
                        v___x_8407_ = lean_apply_13(
                            v___f_8392_,
                            v_a_8406_,
                            v___y_8393_,
                            v___y_8394_,
                            v___y_8395_,
                            v___y_8396_,
                            v___y_8397_,
                            v___y_8398_,
                            v___y_8399_,
                            v___y_8400_,
                            v___y_8401_,
                            v___y_8402_,
                            v___y_8403_,
                            lean_box(0),
                        );
                        return v___x_8407_;
                    } else {
                        lean_dec_ref(v___f_8392_);
                        v_a_8408_ = lean_ctor_get(v___x_8405_, 0);
                        v_isSharedCheck_8415_ = (!lean_is_exclusive(v___x_8405_)) as u8;
                        if v_isSharedCheck_8415_ == 0 {
                            v___x_8410_ = v___x_8405_;
                            v_isShared_8411_ = v_isSharedCheck_8415_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8408_);
                            lean_dec(v___x_8405_);
                            v___x_8410_ = lean_box(0);
                            v_isShared_8411_ = v_isSharedCheck_8415_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_8416_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg(
                        v___y_8393_,
                        v___y_8394_,
                        v___y_8400_,
                        v___y_8401_,
                        v___y_8402_,
                        v___y_8403_,
                    );
                    if lean_obj_tag(v___x_8416_) == 0 {
                        v_a_8417_ = lean_ctor_get(v___x_8416_, 0);
                        lean_inc(v_a_8417_);
                        lean_dec_ref_known(v___x_8416_, 1);
                        lean_inc(v___y_8403_);
                        lean_inc_ref(v___y_8402_);
                        lean_inc(v___y_8401_);
                        lean_inc_ref(v___y_8400_);
                        lean_inc(v___y_8399_);
                        lean_inc_ref(v___y_8398_);
                        lean_inc(v___y_8397_);
                        lean_inc_ref(v___y_8396_);
                        lean_inc(v___y_8395_);
                        lean_inc(v___y_8394_);
                        lean_inc(v___y_8393_);
                        v___x_8418_ = lean_apply_13(
                            v___f_8392_,
                            v_a_8417_,
                            v___y_8393_,
                            v___y_8394_,
                            v___y_8395_,
                            v___y_8396_,
                            v___y_8397_,
                            v___y_8398_,
                            v___y_8399_,
                            v___y_8400_,
                            v___y_8401_,
                            v___y_8402_,
                            v___y_8403_,
                            lean_box(0),
                        );
                        return v___x_8418_;
                    } else {
                        lean_dec_ref(v___f_8392_);
                        v_a_8419_ = lean_ctor_get(v___x_8416_, 0);
                        v_isSharedCheck_8426_ = (!lean_is_exclusive(v___x_8416_)) as u8;
                        if v_isSharedCheck_8426_ == 0 {
                            v___x_8421_ = v___x_8416_;
                            v_isShared_8422_ = v_isSharedCheck_8426_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_8419_);
                            lean_dec(v___x_8416_);
                            v___x_8421_ = lean_box(0);
                            v_isShared_8422_ = v_isSharedCheck_8426_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_8411_ == 0 {
                    v___x_8413_ = v___x_8410_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8414_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8414_, 0, v_a_8408_);
                    v___x_8413_ = v_reuseFailAlloc_8414_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8413_;
            }
            3 => {
                if v_isShared_8422_ == 0 {
                    v___x_8424_ = v___x_8421_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8425_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8425_, 0, v_a_8419_);
                    v___x_8424_ = v_reuseFailAlloc_8425_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8424_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed(
    mut v_eqTrue_8427_: *mut LeanObject,
    mut v___f_8428_: *mut LeanObject,
    mut v___y_8429_: *mut LeanObject,
    mut v___y_8430_: *mut LeanObject,
    mut v___y_8431_: *mut LeanObject,
    mut v___y_8432_: *mut LeanObject,
    mut v___y_8433_: *mut LeanObject,
    mut v___y_8434_: *mut LeanObject,
    mut v___y_8435_: *mut LeanObject,
    mut v___y_8436_: *mut LeanObject,
    mut v___y_8437_: *mut LeanObject,
    mut v___y_8438_: *mut LeanObject,
    mut v___y_8439_: *mut LeanObject,
    mut v___y_8440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eqTrue_boxed_8441_: u8 = 0;
    let mut v_res_8442_: *mut LeanObject = core::ptr::null_mut();
    v_eqTrue_boxed_8441_ = (lean_unbox(v_eqTrue_8427_) as u8);
    v_res_8442_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(
        v_eqTrue_boxed_8441_,
        v___f_8428_,
        v___y_8429_,
        v___y_8430_,
        v___y_8431_,
        v___y_8432_,
        v___y_8433_,
        v___y_8434_,
        v___y_8435_,
        v___y_8436_,
        v___y_8437_,
        v___y_8438_,
        v___y_8439_,
    );
    lean_dec(v___y_8439_);
    lean_dec_ref(v___y_8438_);
    lean_dec(v___y_8437_);
    lean_dec_ref(v___y_8436_);
    lean_dec(v___y_8435_);
    lean_dec_ref(v___y_8434_);
    lean_dec(v___y_8433_);
    lean_dec_ref(v___y_8432_);
    lean_dec(v___y_8431_);
    lean_dec(v___y_8430_);
    lean_dec(v___y_8429_);
    return v_res_8442_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(
    mut v_e_8448_: *mut LeanObject,
    mut v_eqTrue_8449_: u8,
    mut v_a_8450_: *mut LeanObject,
    mut v_a_8451_: *mut LeanObject,
    mut v_a_8452_: *mut LeanObject,
    mut v_a_8453_: *mut LeanObject,
    mut v_a_8454_: *mut LeanObject,
    mut v_a_8455_: *mut LeanObject,
    mut v_a_8456_: *mut LeanObject,
    mut v_a_8457_: *mut LeanObject,
    mut v_a_8458_: *mut LeanObject,
    mut v_a_8459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8468_: u8 = 0;
    let mut v_lia_8469_: u8 = 0;
    let mut v___x_8470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8475_: u8 = 0;
    let mut v_arg_8476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8478_: u8 = 0;
    let mut v_arg_8479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8481_: u8 = 0;
    let mut v___x_8482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8483_: u8 = 0;
    let mut v_arg_8484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8487_: u8 = 0;
    let mut v___x_8488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8493_: u8 = 0;
    let mut v_a_8494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8497_: u8 = 0;
    let mut v___x_8499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8464_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_8452_);
                if lean_obj_tag(v___x_8464_) == 0 {
                    v_a_8465_ = lean_ctor_get(v___x_8464_, 0);
                    v_isSharedCheck_8493_ = (!lean_is_exclusive(v___x_8464_)) as u8;
                    if v_isSharedCheck_8493_ == 0 {
                        v___x_8467_ = v___x_8464_;
                        v_isShared_8468_ = v_isSharedCheck_8493_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_8465_);
                        lean_dec(v___x_8464_);
                        v___x_8467_ = lean_box(0);
                        v_isShared_8468_ = v_isSharedCheck_8493_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_8448_);
                    v_a_8494_ = lean_ctor_get(v___x_8464_, 0);
                    v_isSharedCheck_8501_ = (!lean_is_exclusive(v___x_8464_)) as u8;
                    if v_isSharedCheck_8501_ == 0 {
                        v___x_8496_ = v___x_8464_;
                        v_isShared_8497_ = v_isSharedCheck_8501_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_8494_);
                        lean_dec(v___x_8464_);
                        v___x_8496_ = lean_box(0);
                        v_isShared_8497_ = v_isSharedCheck_8501_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8462_ = lean_box(0);
                v___x_8463_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8463_, 0, v___x_8462_);
                return v___x_8463_;
            }
            2 => {
                v_lia_8469_ = lean_ctor_get_uint8(
                    v_a_8465_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 23) as u32,
                );
                lean_dec(v_a_8465_);
                if v_lia_8469_ == 0 {
                    lean_dec_ref(v_e_8448_);
                    v___x_8470_ = lean_box(0);
                    if v_isShared_8468_ == 0 {
                        lean_ctor_set(v___x_8467_, 0, v___x_8470_);
                        v___x_8472_ = v___x_8467_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8473_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8473_, 0, v___x_8470_);
                        v___x_8472_ = v_reuseFailAlloc_8473_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8467_);
                    lean_inc_ref(v_e_8448_);
                    v___x_8474_ = l_Lean_Expr_cleanupAnnotations(v_e_8448_);
                    v___x_8475_ = l_Lean_Expr_isApp(v___x_8474_);
                    if v___x_8475_ == 0 {
                        lean_dec_ref(v___x_8474_);
                        lean_dec_ref(v_e_8448_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_8476_ = lean_ctor_get(v___x_8474_, 1);
                        lean_inc_ref(v_arg_8476_);
                        v___x_8477_ = l_Lean_Expr_appFnCleanup___redArg(v___x_8474_);
                        v___x_8478_ = l_Lean_Expr_isApp(v___x_8477_);
                        if v___x_8478_ == 0 {
                            lean_dec_ref(v___x_8477_);
                            lean_dec_ref(v_arg_8476_);
                            lean_dec_ref(v_e_8448_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_8479_ = lean_ctor_get(v___x_8477_, 1);
                            lean_inc_ref(v_arg_8479_);
                            v___x_8480_ = l_Lean_Expr_appFnCleanup___redArg(v___x_8477_);
                            v___x_8481_ = l_Lean_Expr_isApp(v___x_8480_);
                            if v___x_8481_ == 0 {
                                lean_dec_ref(v___x_8480_);
                                lean_dec_ref(v_arg_8479_);
                                lean_dec_ref(v_arg_8476_);
                                lean_dec_ref(v_e_8448_);
                                state = 1;
                                continue;
                            } else {
                                v___x_8482_ = l_Lean_Expr_appFnCleanup___redArg(v___x_8480_);
                                v___x_8483_ = l_Lean_Expr_isApp(v___x_8482_);
                                if v___x_8483_ == 0 {
                                    lean_dec_ref(v___x_8482_);
                                    lean_dec_ref(v_arg_8479_);
                                    lean_dec_ref(v_arg_8476_);
                                    lean_dec_ref(v_e_8448_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_8484_ = lean_ctor_get(v___x_8482_, 1);
                                    lean_inc_ref(v_arg_8484_);
                                    v___x_8485_ = l_Lean_Expr_appFnCleanup___redArg(v___x_8482_);
                                    v___x_8486_ =
                                        l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2;
                                    v___x_8487_ = l_Lean_Expr_isConstOf(v___x_8485_, v___x_8486_);
                                    lean_dec_ref(v___x_8485_);
                                    if v___x_8487_ == 0 {
                                        lean_dec_ref(v_arg_8484_);
                                        lean_dec_ref(v_arg_8479_);
                                        lean_dec_ref(v_arg_8476_);
                                        lean_dec_ref(v_e_8448_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_8488_ = lean_box((v_eqTrue_8449_) as usize);
                                        v___f_8489_ = lean_alloc_closure(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed as *mut core::ffi::c_void, 17, 4);
                                        lean_closure_set(v___f_8489_, 0, v_e_8448_);
                                        lean_closure_set(v___f_8489_, 1, v_arg_8479_);
                                        lean_closure_set(v___f_8489_, 2, v_arg_8476_);
                                        lean_closure_set(v___f_8489_, 3, v___x_8488_);
                                        v___x_8490_ = lean_box((v_eqTrue_8449_) as usize);
                                        v___y_8491_ = lean_alloc_closure(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed as *mut core::ffi::c_void, 14, 2);
                                        lean_closure_set(v___y_8491_, 0, v___x_8490_);
                                        lean_closure_set(v___y_8491_, 1, v___f_8489_);
                                        v___x_8492_ = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(
                                            v_arg_8484_,
                                            v___y_8491_,
                                            v_a_8450_,
                                            v_a_8451_,
                                            v_a_8452_,
                                            v_a_8453_,
                                            v_a_8454_,
                                            v_a_8455_,
                                            v_a_8456_,
                                            v_a_8457_,
                                            v_a_8458_,
                                            v_a_8459_,
                                        );
                                        return v___x_8492_;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                return v___x_8472_;
            }
            4 => {
                if v_isShared_8497_ == 0 {
                    v___x_8499_ = v___x_8496_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8500_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8500_, 0, v_a_8494_);
                    v___x_8499_ = v_reuseFailAlloc_8500_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8499_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___boxed(
    mut v_e_8502_: *mut LeanObject,
    mut v_eqTrue_8503_: *mut LeanObject,
    mut v_a_8504_: *mut LeanObject,
    mut v_a_8505_: *mut LeanObject,
    mut v_a_8506_: *mut LeanObject,
    mut v_a_8507_: *mut LeanObject,
    mut v_a_8508_: *mut LeanObject,
    mut v_a_8509_: *mut LeanObject,
    mut v_a_8510_: *mut LeanObject,
    mut v_a_8511_: *mut LeanObject,
    mut v_a_8512_: *mut LeanObject,
    mut v_a_8513_: *mut LeanObject,
    mut v_a_8514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eqTrue_boxed_8515_: u8 = 0;
    let mut v_res_8516_: *mut LeanObject = core::ptr::null_mut();
    v_eqTrue_boxed_8515_ = (lean_unbox(v_eqTrue_8503_) as u8);
    v_res_8516_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(
        v_e_8502_,
        v_eqTrue_boxed_8515_,
        v_a_8504_,
        v_a_8505_,
        v_a_8506_,
        v_a_8507_,
        v_a_8508_,
        v_a_8509_,
        v_a_8510_,
        v_a_8511_,
        v_a_8512_,
        v_a_8513_,
    );
    lean_dec(v_a_8513_);
    lean_dec_ref(v_a_8512_);
    lean_dec(v_a_8511_);
    lean_dec_ref(v_a_8510_);
    lean_dec(v_a_8509_);
    lean_dec_ref(v_a_8508_);
    lean_dec(v_a_8507_);
    lean_dec_ref(v_a_8506_);
    lean_dec(v_a_8505_);
    lean_dec(v_a_8504_);
    return v_res_8516_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_OfNat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_OfNat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Arith_Int(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
}
