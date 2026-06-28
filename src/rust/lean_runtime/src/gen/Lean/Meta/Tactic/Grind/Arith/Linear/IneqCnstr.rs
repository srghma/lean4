// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr
// Imports: Lean.Meta.Tactic.Grind.Arith.Linear.LinearM Lean.Meta.Tactic.Grind.Arith.CommRing.Reify Lean.Meta.Tactic.Grind.Arith.Linear.Den Lean.Meta.Tactic.Grind.Arith.Linear.StructId Lean.Meta.Tactic.Grind.Arith.Linear.Reify Lean.Meta.Tactic.Grind.Arith.Linear.Proof
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Grind::Ordered::Linarith::l_Lean_Grind_Linarith_Expr_norm;
use crate::r#gen::Init::Grind::Ring::CommSolver::l_Lean_Grind_CommRing_Expr_toPoly;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
};
use crate::r#gen::Lean::Data::LBool::l_Lean_instBEqLBool_beq;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_get_x21___redArg, l_Lean_PersistentArray_push___redArg,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getRevArg_x21,
    l_Lean_instInhabitedExpr, l_Lean_mkAppB, l_Lean_mkIntLit,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Reify::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify,
    l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Den::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den,
    l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::DenoteExpr::l_Lean_Grind_CommRing_Poly_toIntModuleExpr;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::LinearM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM,
    l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct,
    l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::OfNatModule::{
    l_Lean_Meta_Grind_Arith_Linear_getNatStruct, l_Lean_Meta_Grind_Arith_Linear_ofNatModule,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Proof::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof,
    l_Lean_Meta_Grind_Arith_Linear_setInconsistent,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Reify::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify, l_Lean_Meta_Grind_Arith_Linear_reify_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::StructId::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId,
    l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f,
    l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Types::l_Lean_Meta_Grind_Arith_Linear_linearExt;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Util::{
    l_Lean_Grind_Linarith_Poly_updateOccs, l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied,
    l_Lean_Meta_Grind_Arith_Linear_isLinearOrder, l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing,
    l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_getConfig___redArg, l_Lean_Meta_Grind_getGeneration___redArg,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_eq, lean_int_dec_lt, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64,
    lean_ctor_get_usize, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__0_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 103, 114, 105, 110, 100, 32, 108, 105, 110, 97, 114, 105, 116, 104, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 44, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 111, 114, 100, 101, 114, 101, 100, 32, 109, 111, 100, 117, 108, 101, 0]};
static mut l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__0_value: LeanStringObject<72> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 72, m_capacity: 72, m_length: 71, m_data: [96, 103, 114, 105, 110, 100, 32, 108, 105, 110, 97, 114, 105, 116, 104, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 44, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 111, 114, 100, 101, 114, 101, 100, 32, 105, 110, 116, 32, 109, 111, 100, 117, 108, 101, 0]};
static mut l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value: LeanStringObject<6> =
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
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [108, 105, 110, 97, 114, 105, 116, 104, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__3_value: LeanStringObject<7> =
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
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__4_value: LeanStringObject<8> =
    LeanStringObject {
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
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__4_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value)
                as *mut LeanObject,
            15947788021050471391 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value)
                as *mut LeanObject,
            10740975855909177240 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__4_value)
                as *mut LeanObject,
            7554315655812471663 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__6_value: LeanStringObject<6> =
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
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__6_value)
                as *mut LeanObject,
            14231257465488249300 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value: LeanStringObject<6> =
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
        m_data: [117, 110, 115, 97, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value)
                as *mut LeanObject,
            15947788021050471391 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value)
                as *mut LeanObject,
            10740975855909177240 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value)
                as *mut LeanObject,
            12596714082087128350 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__12_value: LeanStringObject<6> =
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
        m_data: [115, 116, 111, 114, 101, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__12_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value)
                as *mut LeanObject,
            15947788021050471391 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value)
                as *mut LeanObject,
            10740975855909177240 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__3_value)
                as *mut LeanObject,
            11874191766470140998 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__12_value)
                as *mut LeanObject,
            13803741813067519852 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value)
                as *mut LeanObject,
            15947788021050471391 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value)
                as *mut LeanObject,
            10740975855909177240 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__3_value)
                as *mut LeanObject,
            11874191766470140998 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(
    mut v_fn_x3f_1914_: *mut LeanObject,
    mut v_inst_1915_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_fn_x3f_1914_) == 1 {
        let mut v_val_1916_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1918_: u8 = 0;
        v_val_1916_ = lean_ctor_get(v_fn_x3f_1914_, 0);
        v___x_1917_ = l_Lean_Expr_appArg_x21(v_val_1916_);
        v___x_1918_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
            v___x_1917_,
            v_inst_1915_,
        );
        lean_dec_ref(v___x_1917_);
        return v___x_1918_;
    } else {
        let mut v___x_1919_: u8 = 0;
        v___x_1919_ = 0;
        return v___x_1919_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf___boxed(
    mut v_fn_x3f_1920_: *mut LeanObject,
    mut v_inst_1921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1922_: u8 = 0;
    let mut v_r_1923_: *mut LeanObject = core::ptr::null_mut();
    v_res_1922_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_fn_x3f_1920_, v_inst_1921_);
    lean_dec_ref(v_inst_1921_);
    lean_dec(v_fn_x3f_1920_);
    v_r_1923_ = lean_box((v_res_1922_) as usize);
    return v_r_1923_;
}
pub unsafe fn l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(
    mut v_c_1924_: *mut LeanObject,
    mut v_x_1925_: *mut LeanObject,
    mut v_x_1926_: usize,
    mut v_x_1927_: usize,
) -> *mut LeanObject {
    let mut v_cs_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_1929_: usize = 0;
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: u8 = 0;
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1935_: u8 = 0;
    let mut v___x_1936_: usize = 0;
    let mut v___x_1937_: usize = 0;
    let mut v___x_1938_: usize = 0;
    let mut v_i_1939_: usize = 0;
    let mut v___x_1940_: usize = 0;
    let mut v_shift_1941_: usize = 0;
    let mut v_v_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1950_: u8 = 0;
    let mut v_unused_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: u8 = 0;
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1958_: u8 = 0;
    let mut v_v_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1967_: u8 = 0;
    let mut v_unused_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1925_) == 0 {
                    v_cs_1928_ = lean_ctor_get(v_x_1925_, 0);
                    v_j_1929_ = lean_usize_shift_right(v_x_1926_, v_x_1927_);
                    v___x_1930_ = lean_usize_to_nat(v_j_1929_);
                    v___x_1931_ = lean_array_get_size(v_cs_1928_);
                    v___x_1932_ = lean_nat_dec_lt(v___x_1930_, v___x_1931_);
                    if v___x_1932_ == 0 {
                        lean_dec(v___x_1930_);
                        lean_dec_ref(v_c_1924_);
                        return v_x_1925_;
                    } else {
                        lean_inc_ref(v_cs_1928_);
                        v_isSharedCheck_1950_ = (!lean_is_exclusive(v_x_1925_)) as u8;
                        if v_isSharedCheck_1950_ == 0 {
                            v_unused_1951_ = lean_ctor_get(v_x_1925_, 0);
                            lean_dec(v_unused_1951_);
                            v___x_1934_ = v_x_1925_;
                            v_isShared_1935_ = v_isSharedCheck_1950_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_1925_);
                            v___x_1934_ = lean_box(0);
                            v_isShared_1935_ = v_isSharedCheck_1950_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_vs_1952_ = lean_ctor_get(v_x_1925_, 0);
                    v___x_1953_ = lean_usize_to_nat(v_x_1926_);
                    v___x_1954_ = lean_array_get_size(v_vs_1952_);
                    v___x_1955_ = lean_nat_dec_lt(v___x_1953_, v___x_1954_);
                    if v___x_1955_ == 0 {
                        lean_dec(v___x_1953_);
                        lean_dec_ref(v_c_1924_);
                        return v_x_1925_;
                    } else {
                        lean_inc_ref(v_vs_1952_);
                        v_isSharedCheck_1967_ = (!lean_is_exclusive(v_x_1925_)) as u8;
                        if v_isSharedCheck_1967_ == 0 {
                            v_unused_1968_ = lean_ctor_get(v_x_1925_, 0);
                            lean_dec(v_unused_1968_);
                            v___x_1957_ = v_x_1925_;
                            v_isShared_1958_ = v_isSharedCheck_1967_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v_x_1925_);
                            v___x_1957_ = lean_box(0);
                            v_isShared_1958_ = v_isSharedCheck_1967_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1936_ = 1usize;
                v___x_1937_ = lean_usize_shift_left(v___x_1936_, v_x_1927_);
                v___x_1938_ = lean_usize_sub(v___x_1937_, v___x_1936_);
                v_i_1939_ = lean_usize_land(v_x_1926_, v___x_1938_);
                v___x_1940_ = 5usize;
                v_shift_1941_ = lean_usize_sub(v_x_1927_, v___x_1940_);
                v_v_1942_ = lean_array_fget(v_cs_1928_, v___x_1930_);
                v___x_1943_ = lean_box(0);
                v_xs_x27_1944_ = lean_array_fset(v_cs_1928_, v___x_1930_, v___x_1943_);
                v___x_1945_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(v_c_1924_, v_v_1942_, v_i_1939_, v_shift_1941_);
                v___x_1946_ = lean_array_fset(v_xs_x27_1944_, v___x_1930_, v___x_1945_);
                lean_dec(v___x_1930_);
                if v_isShared_1935_ == 0 {
                    lean_ctor_set(v___x_1934_, 0, v___x_1946_);
                    v___x_1948_ = v___x_1934_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1946_);
                    v___x_1948_ = v_reuseFailAlloc_1949_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1948_;
            }
            3 => {
                v_v_1959_ = lean_array_fget(v_vs_1952_, v___x_1953_);
                v___x_1960_ = lean_box(0);
                v_xs_x27_1961_ = lean_array_fset(v_vs_1952_, v___x_1953_, v___x_1960_);
                v___x_1962_ = l_Lean_PersistentArray_push___redArg(v_v_1959_, v_c_1924_);
                v___x_1963_ = lean_array_fset(v_xs_x27_1961_, v___x_1953_, v___x_1962_);
                lean_dec(v___x_1953_);
                if v_isShared_1958_ == 0 {
                    lean_ctor_set(v___x_1957_, 0, v___x_1963_);
                    v___x_1965_ = v___x_1957_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
                    v___x_1965_ = v_reuseFailAlloc_1966_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1965_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4___boxed(
    mut v_c_1969_: *mut LeanObject,
    mut v_x_1970_: *mut LeanObject,
    mut v_x_1971_: *mut LeanObject,
    mut v_x_1972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_84417__boxed_1973_: usize = 0;
    let mut v_x_84418__boxed_1974_: usize = 0;
    let mut v_res_1975_: *mut LeanObject = core::ptr::null_mut();
    v_x_84417__boxed_1973_ = lean_unbox_usize(v_x_1971_);
    lean_dec(v_x_1971_);
    v_x_84418__boxed_1974_ = lean_unbox_usize(v_x_1972_);
    lean_dec(v_x_1972_);
    v_res_1975_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(v_c_1969_, v_x_1970_, v_x_84417__boxed_1973_, v_x_84418__boxed_1974_);
    return v_res_1975_;
}
pub unsafe fn l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(
    mut v_c_1976_: *mut LeanObject,
    mut v_t_1977_: *mut LeanObject,
    mut v_i_1978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_1982_: usize = 0;
    let mut v_tailOff_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1986_: u8 = 0;
    let mut v___x_1987_: u8 = 0;
    let mut v___x_1988_: usize = 0;
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: u8 = 0;
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2007_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_1979_ = lean_ctor_get(v_t_1977_, 0);
                v_tail_1980_ = lean_ctor_get(v_t_1977_, 1);
                v_size_1981_ = lean_ctor_get(v_t_1977_, 2);
                v_shift_1982_ = lean_ctor_get_usize(v_t_1977_, 4);
                v_tailOff_1983_ = lean_ctor_get(v_t_1977_, 3);
                v_isSharedCheck_2007_ = (!lean_is_exclusive(v_t_1977_)) as u8;
                if v_isSharedCheck_2007_ == 0 {
                    v___x_1985_ = v_t_1977_;
                    v_isShared_1986_ = v_isSharedCheck_2007_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_tailOff_1983_);
                    lean_inc(v_size_1981_);
                    lean_inc(v_tail_1980_);
                    lean_inc(v_root_1979_);
                    lean_dec(v_t_1977_);
                    v___x_1985_ = lean_box(0);
                    v_isShared_1986_ = v_isSharedCheck_2007_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1987_ = lean_nat_dec_le(v_tailOff_1983_, v_i_1978_);
                if v___x_1987_ == 0 {
                    v___x_1988_ = lean_usize_of_nat(v_i_1978_);
                    v___x_1989_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(v_c_1976_, v_root_1979_, v___x_1988_, v_shift_1982_);
                    if v_isShared_1986_ == 0 {
                        lean_ctor_set(v___x_1985_, 0, v___x_1989_);
                        v___x_1991_ = v___x_1985_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1992_ =
                            lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1989_);
                        lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_tail_1980_);
                        lean_ctor_set(v_reuseFailAlloc_1992_, 2, v_size_1981_);
                        lean_ctor_set(v_reuseFailAlloc_1992_, 3, v_tailOff_1983_);
                        lean_ctor_set_usize(v_reuseFailAlloc_1992_, 4, v_shift_1982_);
                        v___x_1991_ = v_reuseFailAlloc_1992_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1993_ = lean_nat_sub(v_i_1978_, v_tailOff_1983_);
                    v___x_1994_ = lean_array_get_size(v_tail_1980_);
                    v___x_1995_ = lean_nat_dec_lt(v___x_1993_, v___x_1994_);
                    if v___x_1995_ == 0 {
                        lean_dec(v___x_1993_);
                        lean_dec_ref(v_c_1976_);
                        if v_isShared_1986_ == 0 {
                            v___x_1997_ = v___x_1985_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1998_ =
                                lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_root_1979_);
                            lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_tail_1980_);
                            lean_ctor_set(v_reuseFailAlloc_1998_, 2, v_size_1981_);
                            lean_ctor_set(v_reuseFailAlloc_1998_, 3, v_tailOff_1983_);
                            lean_ctor_set_usize(v_reuseFailAlloc_1998_, 4, v_shift_1982_);
                            v___x_1997_ = v_reuseFailAlloc_1998_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_v_1999_ = lean_array_fget(v_tail_1980_, v___x_1993_);
                        v___x_2000_ = lean_box(0);
                        v_xs_x27_2001_ = lean_array_fset(v_tail_1980_, v___x_1993_, v___x_2000_);
                        v___x_2002_ = l_Lean_PersistentArray_push___redArg(v_v_1999_, v_c_1976_);
                        v___x_2003_ = lean_array_fset(v_xs_x27_2001_, v___x_1993_, v___x_2002_);
                        lean_dec(v___x_1993_);
                        if v_isShared_1986_ == 0 {
                            lean_ctor_set(v___x_1985_, 1, v___x_2003_);
                            v___x_2005_ = v___x_1985_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2006_ =
                                lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_root_1979_);
                            lean_ctor_set(v_reuseFailAlloc_2006_, 1, v___x_2003_);
                            lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_size_1981_);
                            lean_ctor_set(v_reuseFailAlloc_2006_, 3, v_tailOff_1983_);
                            lean_ctor_set_usize(v_reuseFailAlloc_2006_, 4, v_shift_1982_);
                            v___x_2005_ = v_reuseFailAlloc_2006_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1991_;
            }
            3 => {
                return v___x_1997_;
            }
            4 => {
                return v___x_2005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___boxed(
    mut v_c_2008_: *mut LeanObject,
    mut v_t_2009_: *mut LeanObject,
    mut v_i_2010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2011_: *mut LeanObject = core::ptr::null_mut();
    v_res_2011_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(v_c_2008_, v_t_2009_, v_i_2010_);
    lean_dec(v_i_2010_);
    return v_res_2011_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0(
    mut v___y_2012_: *mut LeanObject,
    mut v_c_2013_: *mut LeanObject,
    mut v_v_2014_: *mut LeanObject,
    mut v_s_2015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_structs_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_forbiddenNatModules_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natStructs_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natTypeIdOf_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNatStructId_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2028_: u8 = 0;
    let mut v_v_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringId_x3f_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intModuleInst_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leInst_x3f_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltInst_x3f_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lawfulOrderLTInst_x3f_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isPreorderInst_x3f_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_orderedAddInst_x3f_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isLinearInst_x3f_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_noNatDivInst_x3f_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_x3f_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_x3f_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_orderedRingInst_x3f_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofNatZero_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leFn_x3f_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltFn_x3f_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zsmulFn_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nsmulFn_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zsmulFn_x3f_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nsmulFn_x3f_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_homomulFn_x3f_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowers_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uppers_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_2066_: u8 = 0;
    let mut v_conflict_x3f_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_occurs_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ignored_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2075_: u8 = 0;
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2086_: u8 = 0;
    let mut v_isSharedCheck_2087_: u8 = 0;
    let mut v_unused_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_2016_ = lean_ctor_get(v_s_2015_, 0);
                v_typeIdOf_2017_ = lean_ctor_get(v_s_2015_, 1);
                v_exprToStructId_2018_ = lean_ctor_get(v_s_2015_, 2);
                v_exprToStructIdEntries_2019_ = lean_ctor_get(v_s_2015_, 3);
                v_forbiddenNatModules_2020_ = lean_ctor_get(v_s_2015_, 4);
                v_natStructs_2021_ = lean_ctor_get(v_s_2015_, 5);
                v_natTypeIdOf_2022_ = lean_ctor_get(v_s_2015_, 6);
                v_exprToNatStructId_2023_ = lean_ctor_get(v_s_2015_, 7);
                v___x_2024_ = lean_array_get_size(v_structs_2016_);
                v___x_2025_ = lean_nat_dec_lt(v___y_2012_, v___x_2024_);
                if v___x_2025_ == 0 {
                    lean_dec_ref(v_c_2013_);
                    return v_s_2015_;
                } else {
                    lean_inc_ref(v_exprToNatStructId_2023_);
                    lean_inc_ref(v_natTypeIdOf_2022_);
                    lean_inc_ref(v_natStructs_2021_);
                    lean_inc_ref(v_forbiddenNatModules_2020_);
                    lean_inc_ref(v_exprToStructIdEntries_2019_);
                    lean_inc_ref(v_exprToStructId_2018_);
                    lean_inc_ref(v_typeIdOf_2017_);
                    lean_inc_ref(v_structs_2016_);
                    v_isSharedCheck_2087_ = (!lean_is_exclusive(v_s_2015_)) as u8;
                    if v_isSharedCheck_2087_ == 0 {
                        v_unused_2088_ = lean_ctor_get(v_s_2015_, 7);
                        lean_dec(v_unused_2088_);
                        v_unused_2089_ = lean_ctor_get(v_s_2015_, 6);
                        lean_dec(v_unused_2089_);
                        v_unused_2090_ = lean_ctor_get(v_s_2015_, 5);
                        lean_dec(v_unused_2090_);
                        v_unused_2091_ = lean_ctor_get(v_s_2015_, 4);
                        lean_dec(v_unused_2091_);
                        v_unused_2092_ = lean_ctor_get(v_s_2015_, 3);
                        lean_dec(v_unused_2092_);
                        v_unused_2093_ = lean_ctor_get(v_s_2015_, 2);
                        lean_dec(v_unused_2093_);
                        v_unused_2094_ = lean_ctor_get(v_s_2015_, 1);
                        lean_dec(v_unused_2094_);
                        v_unused_2095_ = lean_ctor_get(v_s_2015_, 0);
                        lean_dec(v_unused_2095_);
                        v___x_2027_ = v_s_2015_;
                        v_isShared_2028_ = v_isSharedCheck_2087_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_s_2015_);
                        v___x_2027_ = lean_box(0);
                        v_isShared_2028_ = v_isSharedCheck_2087_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2029_ = lean_array_fget(v_structs_2016_, v___y_2012_);
                v_id_2030_ = lean_ctor_get(v_v_2029_, 0);
                v_ringId_x3f_2031_ = lean_ctor_get(v_v_2029_, 1);
                v_type_2032_ = lean_ctor_get(v_v_2029_, 2);
                v_u_2033_ = lean_ctor_get(v_v_2029_, 3);
                v_intModuleInst_2034_ = lean_ctor_get(v_v_2029_, 4);
                v_leInst_x3f_2035_ = lean_ctor_get(v_v_2029_, 5);
                v_ltInst_x3f_2036_ = lean_ctor_get(v_v_2029_, 6);
                v_lawfulOrderLTInst_x3f_2037_ = lean_ctor_get(v_v_2029_, 7);
                v_isPreorderInst_x3f_2038_ = lean_ctor_get(v_v_2029_, 8);
                v_orderedAddInst_x3f_2039_ = lean_ctor_get(v_v_2029_, 9);
                v_isLinearInst_x3f_2040_ = lean_ctor_get(v_v_2029_, 10);
                v_noNatDivInst_x3f_2041_ = lean_ctor_get(v_v_2029_, 11);
                v_ringInst_x3f_2042_ = lean_ctor_get(v_v_2029_, 12);
                v_commRingInst_x3f_2043_ = lean_ctor_get(v_v_2029_, 13);
                v_orderedRingInst_x3f_2044_ = lean_ctor_get(v_v_2029_, 14);
                v_fieldInst_x3f_2045_ = lean_ctor_get(v_v_2029_, 15);
                v_charInst_x3f_2046_ = lean_ctor_get(v_v_2029_, 16);
                v_zero_2047_ = lean_ctor_get(v_v_2029_, 17);
                v_ofNatZero_2048_ = lean_ctor_get(v_v_2029_, 18);
                v_one_x3f_2049_ = lean_ctor_get(v_v_2029_, 19);
                v_leFn_x3f_2050_ = lean_ctor_get(v_v_2029_, 20);
                v_ltFn_x3f_2051_ = lean_ctor_get(v_v_2029_, 21);
                v_addFn_2052_ = lean_ctor_get(v_v_2029_, 22);
                v_zsmulFn_2053_ = lean_ctor_get(v_v_2029_, 23);
                v_nsmulFn_2054_ = lean_ctor_get(v_v_2029_, 24);
                v_zsmulFn_x3f_2055_ = lean_ctor_get(v_v_2029_, 25);
                v_nsmulFn_x3f_2056_ = lean_ctor_get(v_v_2029_, 26);
                v_homomulFn_x3f_2057_ = lean_ctor_get(v_v_2029_, 27);
                v_subFn_2058_ = lean_ctor_get(v_v_2029_, 28);
                v_negFn_2059_ = lean_ctor_get(v_v_2029_, 29);
                v_vars_2060_ = lean_ctor_get(v_v_2029_, 30);
                v_varMap_2061_ = lean_ctor_get(v_v_2029_, 31);
                v_lowers_2062_ = lean_ctor_get(v_v_2029_, 32);
                v_uppers_2063_ = lean_ctor_get(v_v_2029_, 33);
                v_diseqs_2064_ = lean_ctor_get(v_v_2029_, 34);
                v_assignment_2065_ = lean_ctor_get(v_v_2029_, 35);
                v_caseSplits_2066_ = lean_ctor_get_uint8(
                    v_v_2029_,
                    (core::mem::size_of::<*mut LeanObject>() * 42) as u32,
                );
                v_conflict_x3f_2067_ = lean_ctor_get(v_v_2029_, 36);
                v_diseqSplits_2068_ = lean_ctor_get(v_v_2029_, 37);
                v_elimEqs_2069_ = lean_ctor_get(v_v_2029_, 38);
                v_elimStack_2070_ = lean_ctor_get(v_v_2029_, 39);
                v_occurs_2071_ = lean_ctor_get(v_v_2029_, 40);
                v_ignored_2072_ = lean_ctor_get(v_v_2029_, 41);
                v_isSharedCheck_2086_ = (!lean_is_exclusive(v_v_2029_)) as u8;
                if v_isSharedCheck_2086_ == 0 {
                    v___x_2074_ = v_v_2029_;
                    v_isShared_2075_ = v_isSharedCheck_2086_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_ignored_2072_);
                    lean_inc(v_occurs_2071_);
                    lean_inc(v_elimStack_2070_);
                    lean_inc(v_elimEqs_2069_);
                    lean_inc(v_diseqSplits_2068_);
                    lean_inc(v_conflict_x3f_2067_);
                    lean_inc(v_assignment_2065_);
                    lean_inc(v_diseqs_2064_);
                    lean_inc(v_uppers_2063_);
                    lean_inc(v_lowers_2062_);
                    lean_inc(v_varMap_2061_);
                    lean_inc(v_vars_2060_);
                    lean_inc(v_negFn_2059_);
                    lean_inc(v_subFn_2058_);
                    lean_inc(v_homomulFn_x3f_2057_);
                    lean_inc(v_nsmulFn_x3f_2056_);
                    lean_inc(v_zsmulFn_x3f_2055_);
                    lean_inc(v_nsmulFn_2054_);
                    lean_inc(v_zsmulFn_2053_);
                    lean_inc(v_addFn_2052_);
                    lean_inc(v_ltFn_x3f_2051_);
                    lean_inc(v_leFn_x3f_2050_);
                    lean_inc(v_one_x3f_2049_);
                    lean_inc(v_ofNatZero_2048_);
                    lean_inc(v_zero_2047_);
                    lean_inc(v_charInst_x3f_2046_);
                    lean_inc(v_fieldInst_x3f_2045_);
                    lean_inc(v_orderedRingInst_x3f_2044_);
                    lean_inc(v_commRingInst_x3f_2043_);
                    lean_inc(v_ringInst_x3f_2042_);
                    lean_inc(v_noNatDivInst_x3f_2041_);
                    lean_inc(v_isLinearInst_x3f_2040_);
                    lean_inc(v_orderedAddInst_x3f_2039_);
                    lean_inc(v_isPreorderInst_x3f_2038_);
                    lean_inc(v_lawfulOrderLTInst_x3f_2037_);
                    lean_inc(v_ltInst_x3f_2036_);
                    lean_inc(v_leInst_x3f_2035_);
                    lean_inc(v_intModuleInst_2034_);
                    lean_inc(v_u_2033_);
                    lean_inc(v_type_2032_);
                    lean_inc(v_ringId_x3f_2031_);
                    lean_inc(v_id_2030_);
                    lean_dec(v_v_2029_);
                    v___x_2074_ = lean_box(0);
                    v_isShared_2075_ = v_isSharedCheck_2086_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2076_ = lean_box(0);
                v_xs_x27_2077_ = lean_array_fset(v_structs_2016_, v___y_2012_, v___x_2076_);
                v___x_2078_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(v_c_2013_, v_uppers_2063_, v_v_2014_);
                if v_isShared_2075_ == 0 {
                    lean_ctor_set(v___x_2074_, 33, v___x_2078_);
                    v___x_2080_ = v___x_2074_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 42, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_id_2030_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_ringId_x3f_2031_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_type_2032_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_u_2033_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 4, v_intModuleInst_2034_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 5, v_leInst_x3f_2035_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 6, v_ltInst_x3f_2036_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 7, v_lawfulOrderLTInst_x3f_2037_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 8, v_isPreorderInst_x3f_2038_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 9, v_orderedAddInst_x3f_2039_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 10, v_isLinearInst_x3f_2040_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 11, v_noNatDivInst_x3f_2041_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 12, v_ringInst_x3f_2042_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 13, v_commRingInst_x3f_2043_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 14, v_orderedRingInst_x3f_2044_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 15, v_fieldInst_x3f_2045_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 16, v_charInst_x3f_2046_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 17, v_zero_2047_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 18, v_ofNatZero_2048_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 19, v_one_x3f_2049_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 20, v_leFn_x3f_2050_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 21, v_ltFn_x3f_2051_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 22, v_addFn_2052_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 23, v_zsmulFn_2053_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 24, v_nsmulFn_2054_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 25, v_zsmulFn_x3f_2055_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 26, v_nsmulFn_x3f_2056_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 27, v_homomulFn_x3f_2057_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 28, v_subFn_2058_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 29, v_negFn_2059_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 30, v_vars_2060_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 31, v_varMap_2061_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 32, v_lowers_2062_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 33, v___x_2078_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 34, v_diseqs_2064_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 35, v_assignment_2065_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 36, v_conflict_x3f_2067_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 37, v_diseqSplits_2068_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 38, v_elimEqs_2069_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 39, v_elimStack_2070_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 40, v_occurs_2071_);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 41, v_ignored_2072_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2085_,
                        (core::mem::size_of::<*mut LeanObject>() * 42) as u32,
                        v_caseSplits_2066_,
                    );
                    v___x_2080_ = v_reuseFailAlloc_2085_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2081_ = lean_array_fset(v_xs_x27_2077_, v___y_2012_, v___x_2080_);
                if v_isShared_2028_ == 0 {
                    lean_ctor_set(v___x_2027_, 0, v___x_2081_);
                    v___x_2083_ = v___x_2027_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
                    lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_typeIdOf_2017_);
                    lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_exprToStructId_2018_);
                    lean_ctor_set(v_reuseFailAlloc_2084_, 3, v_exprToStructIdEntries_2019_);
                    lean_ctor_set(v_reuseFailAlloc_2084_, 4, v_forbiddenNatModules_2020_);
                    lean_ctor_set(v_reuseFailAlloc_2084_, 5, v_natStructs_2021_);
                    lean_ctor_set(v_reuseFailAlloc_2084_, 6, v_natTypeIdOf_2022_);
                    lean_ctor_set(v_reuseFailAlloc_2084_, 7, v_exprToNatStructId_2023_);
                    v___x_2083_ = v_reuseFailAlloc_2084_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___boxed(
    mut v___y_2096_: *mut LeanObject,
    mut v_c_2097_: *mut LeanObject,
    mut v_v_2098_: *mut LeanObject,
    mut v_s_2099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2100_: *mut LeanObject = core::ptr::null_mut();
    v_res_2100_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0(
        v___y_2096_,
        v_c_2097_,
        v_v_2098_,
        v_s_2099_,
    );
    lean_dec(v_v_2098_);
    lean_dec(v___y_2096_);
    return v_res_2100_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1(
    mut v___y_2101_: *mut LeanObject,
    mut v_c_2102_: *mut LeanObject,
    mut v_v_2103_: *mut LeanObject,
    mut v_s_2104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_structs_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_forbiddenNatModules_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natStructs_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natTypeIdOf_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNatStructId_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: u8 = 0;
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2117_: u8 = 0;
    let mut v_v_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringId_x3f_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intModuleInst_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leInst_x3f_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltInst_x3f_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lawfulOrderLTInst_x3f_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isPreorderInst_x3f_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_orderedAddInst_x3f_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isLinearInst_x3f_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_noNatDivInst_x3f_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_x3f_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_x3f_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_orderedRingInst_x3f_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofNatZero_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leFn_x3f_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltFn_x3f_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zsmulFn_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nsmulFn_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zsmulFn_x3f_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nsmulFn_x3f_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_homomulFn_x3f_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowers_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uppers_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_2155_: u8 = 0;
    let mut v_conflict_x3f_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_occurs_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ignored_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2164_: u8 = 0;
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2175_: u8 = 0;
    let mut v_isSharedCheck_2176_: u8 = 0;
    let mut v_unused_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_2105_ = lean_ctor_get(v_s_2104_, 0);
                v_typeIdOf_2106_ = lean_ctor_get(v_s_2104_, 1);
                v_exprToStructId_2107_ = lean_ctor_get(v_s_2104_, 2);
                v_exprToStructIdEntries_2108_ = lean_ctor_get(v_s_2104_, 3);
                v_forbiddenNatModules_2109_ = lean_ctor_get(v_s_2104_, 4);
                v_natStructs_2110_ = lean_ctor_get(v_s_2104_, 5);
                v_natTypeIdOf_2111_ = lean_ctor_get(v_s_2104_, 6);
                v_exprToNatStructId_2112_ = lean_ctor_get(v_s_2104_, 7);
                v___x_2113_ = lean_array_get_size(v_structs_2105_);
                v___x_2114_ = lean_nat_dec_lt(v___y_2101_, v___x_2113_);
                if v___x_2114_ == 0 {
                    lean_dec_ref(v_c_2102_);
                    return v_s_2104_;
                } else {
                    lean_inc_ref(v_exprToNatStructId_2112_);
                    lean_inc_ref(v_natTypeIdOf_2111_);
                    lean_inc_ref(v_natStructs_2110_);
                    lean_inc_ref(v_forbiddenNatModules_2109_);
                    lean_inc_ref(v_exprToStructIdEntries_2108_);
                    lean_inc_ref(v_exprToStructId_2107_);
                    lean_inc_ref(v_typeIdOf_2106_);
                    lean_inc_ref(v_structs_2105_);
                    v_isSharedCheck_2176_ = (!lean_is_exclusive(v_s_2104_)) as u8;
                    if v_isSharedCheck_2176_ == 0 {
                        v_unused_2177_ = lean_ctor_get(v_s_2104_, 7);
                        lean_dec(v_unused_2177_);
                        v_unused_2178_ = lean_ctor_get(v_s_2104_, 6);
                        lean_dec(v_unused_2178_);
                        v_unused_2179_ = lean_ctor_get(v_s_2104_, 5);
                        lean_dec(v_unused_2179_);
                        v_unused_2180_ = lean_ctor_get(v_s_2104_, 4);
                        lean_dec(v_unused_2180_);
                        v_unused_2181_ = lean_ctor_get(v_s_2104_, 3);
                        lean_dec(v_unused_2181_);
                        v_unused_2182_ = lean_ctor_get(v_s_2104_, 2);
                        lean_dec(v_unused_2182_);
                        v_unused_2183_ = lean_ctor_get(v_s_2104_, 1);
                        lean_dec(v_unused_2183_);
                        v_unused_2184_ = lean_ctor_get(v_s_2104_, 0);
                        lean_dec(v_unused_2184_);
                        v___x_2116_ = v_s_2104_;
                        v_isShared_2117_ = v_isSharedCheck_2176_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_s_2104_);
                        v___x_2116_ = lean_box(0);
                        v_isShared_2117_ = v_isSharedCheck_2176_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2118_ = lean_array_fget(v_structs_2105_, v___y_2101_);
                v_id_2119_ = lean_ctor_get(v_v_2118_, 0);
                v_ringId_x3f_2120_ = lean_ctor_get(v_v_2118_, 1);
                v_type_2121_ = lean_ctor_get(v_v_2118_, 2);
                v_u_2122_ = lean_ctor_get(v_v_2118_, 3);
                v_intModuleInst_2123_ = lean_ctor_get(v_v_2118_, 4);
                v_leInst_x3f_2124_ = lean_ctor_get(v_v_2118_, 5);
                v_ltInst_x3f_2125_ = lean_ctor_get(v_v_2118_, 6);
                v_lawfulOrderLTInst_x3f_2126_ = lean_ctor_get(v_v_2118_, 7);
                v_isPreorderInst_x3f_2127_ = lean_ctor_get(v_v_2118_, 8);
                v_orderedAddInst_x3f_2128_ = lean_ctor_get(v_v_2118_, 9);
                v_isLinearInst_x3f_2129_ = lean_ctor_get(v_v_2118_, 10);
                v_noNatDivInst_x3f_2130_ = lean_ctor_get(v_v_2118_, 11);
                v_ringInst_x3f_2131_ = lean_ctor_get(v_v_2118_, 12);
                v_commRingInst_x3f_2132_ = lean_ctor_get(v_v_2118_, 13);
                v_orderedRingInst_x3f_2133_ = lean_ctor_get(v_v_2118_, 14);
                v_fieldInst_x3f_2134_ = lean_ctor_get(v_v_2118_, 15);
                v_charInst_x3f_2135_ = lean_ctor_get(v_v_2118_, 16);
                v_zero_2136_ = lean_ctor_get(v_v_2118_, 17);
                v_ofNatZero_2137_ = lean_ctor_get(v_v_2118_, 18);
                v_one_x3f_2138_ = lean_ctor_get(v_v_2118_, 19);
                v_leFn_x3f_2139_ = lean_ctor_get(v_v_2118_, 20);
                v_ltFn_x3f_2140_ = lean_ctor_get(v_v_2118_, 21);
                v_addFn_2141_ = lean_ctor_get(v_v_2118_, 22);
                v_zsmulFn_2142_ = lean_ctor_get(v_v_2118_, 23);
                v_nsmulFn_2143_ = lean_ctor_get(v_v_2118_, 24);
                v_zsmulFn_x3f_2144_ = lean_ctor_get(v_v_2118_, 25);
                v_nsmulFn_x3f_2145_ = lean_ctor_get(v_v_2118_, 26);
                v_homomulFn_x3f_2146_ = lean_ctor_get(v_v_2118_, 27);
                v_subFn_2147_ = lean_ctor_get(v_v_2118_, 28);
                v_negFn_2148_ = lean_ctor_get(v_v_2118_, 29);
                v_vars_2149_ = lean_ctor_get(v_v_2118_, 30);
                v_varMap_2150_ = lean_ctor_get(v_v_2118_, 31);
                v_lowers_2151_ = lean_ctor_get(v_v_2118_, 32);
                v_uppers_2152_ = lean_ctor_get(v_v_2118_, 33);
                v_diseqs_2153_ = lean_ctor_get(v_v_2118_, 34);
                v_assignment_2154_ = lean_ctor_get(v_v_2118_, 35);
                v_caseSplits_2155_ = lean_ctor_get_uint8(
                    v_v_2118_,
                    (core::mem::size_of::<*mut LeanObject>() * 42) as u32,
                );
                v_conflict_x3f_2156_ = lean_ctor_get(v_v_2118_, 36);
                v_diseqSplits_2157_ = lean_ctor_get(v_v_2118_, 37);
                v_elimEqs_2158_ = lean_ctor_get(v_v_2118_, 38);
                v_elimStack_2159_ = lean_ctor_get(v_v_2118_, 39);
                v_occurs_2160_ = lean_ctor_get(v_v_2118_, 40);
                v_ignored_2161_ = lean_ctor_get(v_v_2118_, 41);
                v_isSharedCheck_2175_ = (!lean_is_exclusive(v_v_2118_)) as u8;
                if v_isSharedCheck_2175_ == 0 {
                    v___x_2163_ = v_v_2118_;
                    v_isShared_2164_ = v_isSharedCheck_2175_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_ignored_2161_);
                    lean_inc(v_occurs_2160_);
                    lean_inc(v_elimStack_2159_);
                    lean_inc(v_elimEqs_2158_);
                    lean_inc(v_diseqSplits_2157_);
                    lean_inc(v_conflict_x3f_2156_);
                    lean_inc(v_assignment_2154_);
                    lean_inc(v_diseqs_2153_);
                    lean_inc(v_uppers_2152_);
                    lean_inc(v_lowers_2151_);
                    lean_inc(v_varMap_2150_);
                    lean_inc(v_vars_2149_);
                    lean_inc(v_negFn_2148_);
                    lean_inc(v_subFn_2147_);
                    lean_inc(v_homomulFn_x3f_2146_);
                    lean_inc(v_nsmulFn_x3f_2145_);
                    lean_inc(v_zsmulFn_x3f_2144_);
                    lean_inc(v_nsmulFn_2143_);
                    lean_inc(v_zsmulFn_2142_);
                    lean_inc(v_addFn_2141_);
                    lean_inc(v_ltFn_x3f_2140_);
                    lean_inc(v_leFn_x3f_2139_);
                    lean_inc(v_one_x3f_2138_);
                    lean_inc(v_ofNatZero_2137_);
                    lean_inc(v_zero_2136_);
                    lean_inc(v_charInst_x3f_2135_);
                    lean_inc(v_fieldInst_x3f_2134_);
                    lean_inc(v_orderedRingInst_x3f_2133_);
                    lean_inc(v_commRingInst_x3f_2132_);
                    lean_inc(v_ringInst_x3f_2131_);
                    lean_inc(v_noNatDivInst_x3f_2130_);
                    lean_inc(v_isLinearInst_x3f_2129_);
                    lean_inc(v_orderedAddInst_x3f_2128_);
                    lean_inc(v_isPreorderInst_x3f_2127_);
                    lean_inc(v_lawfulOrderLTInst_x3f_2126_);
                    lean_inc(v_ltInst_x3f_2125_);
                    lean_inc(v_leInst_x3f_2124_);
                    lean_inc(v_intModuleInst_2123_);
                    lean_inc(v_u_2122_);
                    lean_inc(v_type_2121_);
                    lean_inc(v_ringId_x3f_2120_);
                    lean_inc(v_id_2119_);
                    lean_dec(v_v_2118_);
                    v___x_2163_ = lean_box(0);
                    v_isShared_2164_ = v_isSharedCheck_2175_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2165_ = lean_box(0);
                v_xs_x27_2166_ = lean_array_fset(v_structs_2105_, v___y_2101_, v___x_2165_);
                v___x_2167_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(v_c_2102_, v_lowers_2151_, v_v_2103_);
                if v_isShared_2164_ == 0 {
                    lean_ctor_set(v___x_2163_, 32, v___x_2167_);
                    v___x_2169_ = v___x_2163_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 42, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_id_2119_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_ringId_x3f_2120_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 2, v_type_2121_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 3, v_u_2122_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 4, v_intModuleInst_2123_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 5, v_leInst_x3f_2124_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 6, v_ltInst_x3f_2125_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 7, v_lawfulOrderLTInst_x3f_2126_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 8, v_isPreorderInst_x3f_2127_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 9, v_orderedAddInst_x3f_2128_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 10, v_isLinearInst_x3f_2129_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 11, v_noNatDivInst_x3f_2130_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 12, v_ringInst_x3f_2131_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 13, v_commRingInst_x3f_2132_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 14, v_orderedRingInst_x3f_2133_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 15, v_fieldInst_x3f_2134_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 16, v_charInst_x3f_2135_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 17, v_zero_2136_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 18, v_ofNatZero_2137_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 19, v_one_x3f_2138_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 20, v_leFn_x3f_2139_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 21, v_ltFn_x3f_2140_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 22, v_addFn_2141_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 23, v_zsmulFn_2142_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 24, v_nsmulFn_2143_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 25, v_zsmulFn_x3f_2144_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 26, v_nsmulFn_x3f_2145_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 27, v_homomulFn_x3f_2146_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 28, v_subFn_2147_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 29, v_negFn_2148_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 30, v_vars_2149_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 31, v_varMap_2150_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 32, v___x_2167_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 33, v_uppers_2152_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 34, v_diseqs_2153_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 35, v_assignment_2154_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 36, v_conflict_x3f_2156_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 37, v_diseqSplits_2157_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 38, v_elimEqs_2158_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 39, v_elimStack_2159_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 40, v_occurs_2160_);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 41, v_ignored_2161_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2174_,
                        (core::mem::size_of::<*mut LeanObject>() * 42) as u32,
                        v_caseSplits_2155_,
                    );
                    v___x_2169_ = v_reuseFailAlloc_2174_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2170_ = lean_array_fset(v_xs_x27_2166_, v___y_2101_, v___x_2169_);
                if v_isShared_2117_ == 0 {
                    lean_ctor_set(v___x_2116_, 0, v___x_2170_);
                    v___x_2172_ = v___x_2116_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2170_);
                    lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_typeIdOf_2106_);
                    lean_ctor_set(v_reuseFailAlloc_2173_, 2, v_exprToStructId_2107_);
                    lean_ctor_set(v_reuseFailAlloc_2173_, 3, v_exprToStructIdEntries_2108_);
                    lean_ctor_set(v_reuseFailAlloc_2173_, 4, v_forbiddenNatModules_2109_);
                    lean_ctor_set(v_reuseFailAlloc_2173_, 5, v_natStructs_2110_);
                    lean_ctor_set(v_reuseFailAlloc_2173_, 6, v_natTypeIdOf_2111_);
                    lean_ctor_set(v_reuseFailAlloc_2173_, 7, v_exprToNatStructId_2112_);
                    v___x_2172_ = v_reuseFailAlloc_2173_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2172_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1___boxed(
    mut v___y_2185_: *mut LeanObject,
    mut v_c_2186_: *mut LeanObject,
    mut v_v_2187_: *mut LeanObject,
    mut v_s_2188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2189_: *mut LeanObject = core::ptr::null_mut();
    v_res_2189_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1(
        v___y_2185_,
        v_c_2186_,
        v_v_2187_,
        v_s_2188_,
    );
    lean_dec(v_v_2187_);
    lean_dec(v___y_2185_);
    return v_res_2189_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0()
-> *mut LeanObject {
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    v___x_2190_ = lean_unsigned_to_nat(1);
    v___x_2191_ = lean_nat_to_int(v___x_2190_);
    return v___x_2191_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(
    mut v_k_2192_: *mut LeanObject,
    mut v_x_2193_: *mut LeanObject,
    mut v___y_2194_: *mut LeanObject,
    mut v___y_2195_: *mut LeanObject,
    mut v___y_2196_: *mut LeanObject,
    mut v___y_2197_: *mut LeanObject,
    mut v___y_2198_: *mut LeanObject,
    mut v___y_2199_: *mut LeanObject,
    mut v___y_2200_: *mut LeanObject,
    mut v___y_2201_: *mut LeanObject,
    mut v___y_2202_: *mut LeanObject,
    mut v___y_2203_: *mut LeanObject,
    mut v___y_2204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: u8 = 0;
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2214_: u8 = 0;
    let mut v_vars_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zsmulFn_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: u8 = 0;
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2229_: u8 = 0;
    let mut v_a_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2233_: u8 = 0;
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut v_a_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2241_: u8 = 0;
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2245_: u8 = 0;
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2250_: u8 = 0;
    let mut v_vars_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: u8 = 0;
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2263_: u8 = 0;
    let mut v_a_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2267_: u8 = 0;
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2271_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2206_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0);
                v___x_2207_ = lean_int_dec_eq(v_k_2192_, v___x_2206_);
                if v___x_2207_ == 0 {
                    v___x_2208_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                        v___y_2194_,
                        v___y_2195_,
                        v___y_2196_,
                        v___y_2197_,
                        v___y_2198_,
                        v___y_2199_,
                        v___y_2200_,
                        v___y_2201_,
                        v___y_2202_,
                        v___y_2203_,
                        v___y_2204_,
                    );
                    if lean_obj_tag(v___x_2208_) == 0 {
                        v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
                        lean_inc(v_a_2209_);
                        lean_dec_ref_known(v___x_2208_, 1);
                        v___x_2210_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                            v___y_2194_,
                            v___y_2195_,
                            v___y_2196_,
                            v___y_2197_,
                            v___y_2198_,
                            v___y_2199_,
                            v___y_2200_,
                            v___y_2201_,
                            v___y_2202_,
                            v___y_2203_,
                            v___y_2204_,
                        );
                        if lean_obj_tag(v___x_2210_) == 0 {
                            v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
                            v_isSharedCheck_2229_ = (!lean_is_exclusive(v___x_2210_)) as u8;
                            if v_isSharedCheck_2229_ == 0 {
                                v___x_2213_ = v___x_2210_;
                                v_isShared_2214_ = v_isSharedCheck_2229_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2211_);
                                lean_dec(v___x_2210_);
                                v___x_2213_ = lean_box(0);
                                v_isShared_2214_ = v_isSharedCheck_2229_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2209_);
                            v_a_2230_ = lean_ctor_get(v___x_2210_, 0);
                            v_isSharedCheck_2237_ = (!lean_is_exclusive(v___x_2210_)) as u8;
                            if v_isSharedCheck_2237_ == 0 {
                                v___x_2232_ = v___x_2210_;
                                v_isShared_2233_ = v_isSharedCheck_2237_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_2230_);
                                lean_dec(v___x_2210_);
                                v___x_2232_ = lean_box(0);
                                v_isShared_2233_ = v_isSharedCheck_2237_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_a_2238_ = lean_ctor_get(v___x_2208_, 0);
                        v_isSharedCheck_2245_ = (!lean_is_exclusive(v___x_2208_)) as u8;
                        if v_isSharedCheck_2245_ == 0 {
                            v___x_2240_ = v___x_2208_;
                            v_isShared_2241_ = v_isSharedCheck_2245_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2238_);
                            lean_dec(v___x_2208_);
                            v___x_2240_ = lean_box(0);
                            v_isShared_2241_ = v_isSharedCheck_2245_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v___x_2246_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                        v___y_2194_,
                        v___y_2195_,
                        v___y_2196_,
                        v___y_2197_,
                        v___y_2198_,
                        v___y_2199_,
                        v___y_2200_,
                        v___y_2201_,
                        v___y_2202_,
                        v___y_2203_,
                        v___y_2204_,
                    );
                    if lean_obj_tag(v___x_2246_) == 0 {
                        v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
                        v_isSharedCheck_2263_ = (!lean_is_exclusive(v___x_2246_)) as u8;
                        if v_isSharedCheck_2263_ == 0 {
                            v___x_2249_ = v___x_2246_;
                            v_isShared_2250_ = v_isSharedCheck_2263_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_2247_);
                            lean_dec(v___x_2246_);
                            v___x_2249_ = lean_box(0);
                            v_isShared_2250_ = v_isSharedCheck_2263_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_a_2264_ = lean_ctor_get(v___x_2246_, 0);
                        v_isSharedCheck_2271_ = (!lean_is_exclusive(v___x_2246_)) as u8;
                        if v_isSharedCheck_2271_ == 0 {
                            v___x_2266_ = v___x_2246_;
                            v_isShared_2267_ = v_isSharedCheck_2271_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_2264_);
                            lean_dec(v___x_2246_);
                            v___x_2266_ = lean_box(0);
                            v_isShared_2267_ = v_isSharedCheck_2271_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_vars_2215_ = lean_ctor_get(v_a_2211_, 30);
                lean_inc_ref(v_vars_2215_);
                lean_dec(v_a_2211_);
                v_zsmulFn_2216_ = lean_ctor_get(v_a_2209_, 23);
                lean_inc_ref(v_zsmulFn_2216_);
                lean_dec(v_a_2209_);
                v_size_2217_ = lean_ctor_get(v_vars_2215_, 2);
                v___x_2218_ = l_Lean_mkIntLit(v_k_2192_);
                v___x_2225_ = l_Lean_instInhabitedExpr;
                v___x_2226_ = lean_nat_dec_lt(v_x_2193_, v_size_2217_);
                if v___x_2226_ == 0 {
                    lean_dec_ref(v_vars_2215_);
                    v___x_2227_ = l_outOfBounds___redArg(v___x_2225_);
                    v___y_2220_ = v___x_2227_;
                    state = 2;
                    continue;
                } else {
                    v___x_2228_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_2225_,
                        v_vars_2215_,
                        v_x_2193_,
                    );
                    lean_dec_ref(v_vars_2215_);
                    v___y_2220_ = v___x_2228_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2221_ = l_Lean_mkAppB(v_zsmulFn_2216_, v___x_2218_, v___y_2220_);
                if v_isShared_2214_ == 0 {
                    lean_ctor_set(v___x_2213_, 0, v___x_2221_);
                    v___x_2223_ = v___x_2213_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2221_);
                    v___x_2223_ = v_reuseFailAlloc_2224_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2223_;
            }
            4 => {
                if v_isShared_2233_ == 0 {
                    v___x_2235_ = v___x_2232_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
                    v___x_2235_ = v_reuseFailAlloc_2236_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2235_;
            }
            6 => {
                if v_isShared_2241_ == 0 {
                    v___x_2243_ = v___x_2240_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
                    v___x_2243_ = v_reuseFailAlloc_2244_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2243_;
            }
            8 => {
                v_vars_2251_ = lean_ctor_get(v_a_2247_, 30);
                lean_inc_ref(v_vars_2251_);
                lean_dec(v_a_2247_);
                v_size_2252_ = lean_ctor_get(v_vars_2251_, 2);
                v___x_2253_ = l_Lean_instInhabitedExpr;
                v___x_2254_ = lean_nat_dec_lt(v_x_2193_, v_size_2252_);
                if v___x_2254_ == 0 {
                    lean_dec_ref(v_vars_2251_);
                    v___x_2255_ = l_outOfBounds___redArg(v___x_2253_);
                    if v_isShared_2250_ == 0 {
                        lean_ctor_set(v___x_2249_, 0, v___x_2255_);
                        v___x_2257_ = v___x_2249_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2255_);
                        v___x_2257_ = v_reuseFailAlloc_2258_;
                        state = 9;
                        continue;
                    }
                } else {
                    v___x_2259_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_2253_,
                        v_vars_2251_,
                        v_x_2193_,
                    );
                    lean_dec_ref(v_vars_2251_);
                    if v_isShared_2250_ == 0 {
                        lean_ctor_set(v___x_2249_, 0, v___x_2259_);
                        v___x_2261_ = v___x_2249_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
                        v___x_2261_ = v_reuseFailAlloc_2262_;
                        state = 10;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_2257_;
            }
            10 => {
                return v___x_2261_;
            }
            11 => {
                if v_isShared_2267_ == 0 {
                    v___x_2269_ = v___x_2266_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
                    v___x_2269_ = v_reuseFailAlloc_2270_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2269_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___boxed(
    mut v_k_2272_: *mut LeanObject,
    mut v_x_2273_: *mut LeanObject,
    mut v___y_2274_: *mut LeanObject,
    mut v___y_2275_: *mut LeanObject,
    mut v___y_2276_: *mut LeanObject,
    mut v___y_2277_: *mut LeanObject,
    mut v___y_2278_: *mut LeanObject,
    mut v___y_2279_: *mut LeanObject,
    mut v___y_2280_: *mut LeanObject,
    mut v___y_2281_: *mut LeanObject,
    mut v___y_2282_: *mut LeanObject,
    mut v___y_2283_: *mut LeanObject,
    mut v___y_2284_: *mut LeanObject,
    mut v___y_2285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2286_: *mut LeanObject = core::ptr::null_mut();
    v_res_2286_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(v_k_2272_, v_x_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
    lean_dec(v___y_2284_);
    lean_dec_ref(v___y_2283_);
    lean_dec(v___y_2282_);
    lean_dec_ref(v___y_2281_);
    lean_dec(v___y_2280_);
    lean_dec_ref(v___y_2279_);
    lean_dec(v___y_2278_);
    lean_dec_ref(v___y_2277_);
    lean_dec(v___y_2276_);
    lean_dec(v___y_2275_);
    lean_dec(v___y_2274_);
    lean_dec(v_x_2273_);
    lean_dec(v_k_2272_);
    return v_res_2286_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8(
    mut v_p_2287_: *mut LeanObject,
    mut v_acc_2288_: *mut LeanObject,
    mut v___y_2289_: *mut LeanObject,
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
) -> *mut LeanObject {
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2315_: u8 = 0;
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_2287_) == 0 {
                    v___x_2301_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2301_, 0, v_acc_2288_);
                    return v___x_2301_;
                } else {
                    v_k_2302_ = lean_ctor_get(v_p_2287_, 0);
                    v_v_2303_ = lean_ctor_get(v_p_2287_, 1);
                    v_p_2304_ = lean_ctor_get(v_p_2287_, 2);
                    v___x_2305_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                        v___y_2289_,
                        v___y_2290_,
                        v___y_2291_,
                        v___y_2292_,
                        v___y_2293_,
                        v___y_2294_,
                        v___y_2295_,
                        v___y_2296_,
                        v___y_2297_,
                        v___y_2298_,
                        v___y_2299_,
                    );
                    if lean_obj_tag(v___x_2305_) == 0 {
                        v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
                        lean_inc(v_a_2306_);
                        lean_dec_ref_known(v___x_2305_, 1);
                        v___x_2307_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(v_k_2302_, v_v_2303_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
                        if lean_obj_tag(v___x_2307_) == 0 {
                            v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
                            lean_inc(v_a_2308_);
                            lean_dec_ref_known(v___x_2307_, 1);
                            v_addFn_2309_ = lean_ctor_get(v_a_2306_, 22);
                            lean_inc_ref(v_addFn_2309_);
                            lean_dec(v_a_2306_);
                            v___x_2310_ = l_Lean_mkAppB(v_addFn_2309_, v_acc_2288_, v_a_2308_);
                            v_p_2287_ = v_p_2304_;
                            v_acc_2288_ = v___x_2310_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_a_2306_);
                            lean_dec_ref(v_acc_2288_);
                            return v___x_2307_;
                        }
                    } else {
                        lean_dec_ref(v_acc_2288_);
                        v_a_2312_ = lean_ctor_get(v___x_2305_, 0);
                        v_isSharedCheck_2319_ = (!lean_is_exclusive(v___x_2305_)) as u8;
                        if v_isSharedCheck_2319_ == 0 {
                            v___x_2314_ = v___x_2305_;
                            v_isShared_2315_ = v_isSharedCheck_2319_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2312_);
                            lean_dec(v___x_2305_);
                            v___x_2314_ = lean_box(0);
                            v_isShared_2315_ = v_isSharedCheck_2319_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2315_ == 0 {
                    v___x_2317_ = v___x_2314_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
                    v___x_2317_ = v_reuseFailAlloc_2318_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2317_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8___boxed(
    mut v_p_2320_: *mut LeanObject,
    mut v_acc_2321_: *mut LeanObject,
    mut v___y_2322_: *mut LeanObject,
    mut v___y_2323_: *mut LeanObject,
    mut v___y_2324_: *mut LeanObject,
    mut v___y_2325_: *mut LeanObject,
    mut v___y_2326_: *mut LeanObject,
    mut v___y_2327_: *mut LeanObject,
    mut v___y_2328_: *mut LeanObject,
    mut v___y_2329_: *mut LeanObject,
    mut v___y_2330_: *mut LeanObject,
    mut v___y_2331_: *mut LeanObject,
    mut v___y_2332_: *mut LeanObject,
    mut v___y_2333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2334_: *mut LeanObject = core::ptr::null_mut();
    v_res_2334_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8(v_p_2320_, v_acc_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
    lean_dec(v___y_2332_);
    lean_dec_ref(v___y_2331_);
    lean_dec(v___y_2330_);
    lean_dec_ref(v___y_2329_);
    lean_dec(v___y_2328_);
    lean_dec_ref(v___y_2327_);
    lean_dec(v___y_2326_);
    lean_dec_ref(v___y_2325_);
    lean_dec(v___y_2324_);
    lean_dec(v___y_2323_);
    lean_dec(v___y_2322_);
    lean_dec(v_p_2320_);
    return v_res_2334_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(
    mut v_p_2335_: *mut LeanObject,
    mut v___y_2336_: *mut LeanObject,
    mut v___y_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
    mut v___y_2339_: *mut LeanObject,
    mut v___y_2340_: *mut LeanObject,
    mut v___y_2341_: *mut LeanObject,
    mut v___y_2342_: *mut LeanObject,
    mut v___y_2343_: *mut LeanObject,
    mut v___y_2344_: *mut LeanObject,
    mut v___y_2345_: *mut LeanObject,
    mut v___y_2346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2352_: u8 = 0;
    let mut v_zero_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2357_: u8 = 0;
    let mut v_a_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2361_: u8 = 0;
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2365_: u8 = 0;
    let mut v_k_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_2335_) == 0 {
                    v___x_2348_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                        v___y_2336_,
                        v___y_2337_,
                        v___y_2338_,
                        v___y_2339_,
                        v___y_2340_,
                        v___y_2341_,
                        v___y_2342_,
                        v___y_2343_,
                        v___y_2344_,
                        v___y_2345_,
                        v___y_2346_,
                    );
                    if lean_obj_tag(v___x_2348_) == 0 {
                        v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
                        v_isSharedCheck_2357_ = (!lean_is_exclusive(v___x_2348_)) as u8;
                        if v_isSharedCheck_2357_ == 0 {
                            v___x_2351_ = v___x_2348_;
                            v_isShared_2352_ = v_isSharedCheck_2357_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2349_);
                            lean_dec(v___x_2348_);
                            v___x_2351_ = lean_box(0);
                            v_isShared_2352_ = v_isSharedCheck_2357_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2358_ = lean_ctor_get(v___x_2348_, 0);
                        v_isSharedCheck_2365_ = (!lean_is_exclusive(v___x_2348_)) as u8;
                        if v_isSharedCheck_2365_ == 0 {
                            v___x_2360_ = v___x_2348_;
                            v_isShared_2361_ = v_isSharedCheck_2365_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2358_);
                            lean_dec(v___x_2348_);
                            v___x_2360_ = lean_box(0);
                            v_isShared_2361_ = v_isSharedCheck_2365_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_k_2366_ = lean_ctor_get(v_p_2335_, 0);
                    v_v_2367_ = lean_ctor_get(v_p_2335_, 1);
                    v_p_2368_ = lean_ctor_get(v_p_2335_, 2);
                    v___x_2369_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(v_k_2366_, v_v_2367_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
                    if lean_obj_tag(v___x_2369_) == 0 {
                        v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
                        lean_inc(v_a_2370_);
                        lean_dec_ref_known(v___x_2369_, 1);
                        v___x_2371_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8(v_p_2368_, v_a_2370_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
                        return v___x_2371_;
                    } else {
                        return v___x_2369_;
                    }
                }
            }
            1 => {
                v_zero_2353_ = lean_ctor_get(v_a_2349_, 17);
                lean_inc_ref(v_zero_2353_);
                lean_dec(v_a_2349_);
                if v_isShared_2352_ == 0 {
                    lean_ctor_set(v___x_2351_, 0, v_zero_2353_);
                    v___x_2355_ = v___x_2351_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_zero_2353_);
                    v___x_2355_ = v_reuseFailAlloc_2356_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2355_;
            }
            3 => {
                if v_isShared_2361_ == 0 {
                    v___x_2363_ = v___x_2360_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
                    v___x_2363_ = v_reuseFailAlloc_2364_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2363_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2___boxed(
    mut v_p_2372_: *mut LeanObject,
    mut v___y_2373_: *mut LeanObject,
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
    let mut v_res_2385_: *mut LeanObject = core::ptr::null_mut();
    v_res_2385_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(v_p_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
    lean_dec(v___y_2383_);
    lean_dec_ref(v___y_2382_);
    lean_dec(v___y_2381_);
    lean_dec_ref(v___y_2380_);
    lean_dec(v___y_2379_);
    lean_dec_ref(v___y_2378_);
    lean_dec(v___y_2377_);
    lean_dec_ref(v___y_2376_);
    lean_dec(v___y_2375_);
    lean_dec(v___y_2374_);
    lean_dec(v___y_2373_);
    lean_dec(v_p_2372_);
    return v_res_2385_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(
    mut v_msgData_2386_: *mut LeanObject,
    mut v___y_2387_: *mut LeanObject,
    mut v___y_2388_: *mut LeanObject,
    mut v___y_2389_: *mut LeanObject,
    mut v___y_2390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    v___x_2392_ = lean_st_ref_get(v___y_2390_);
    v_env_2393_ = lean_ctor_get(v___x_2392_, 0);
    lean_inc_ref(v_env_2393_);
    lean_dec(v___x_2392_);
    v___x_2394_ = lean_st_ref_get(v___y_2388_);
    v_mctx_2395_ = lean_ctor_get(v___x_2394_, 0);
    lean_inc_ref(v_mctx_2395_);
    lean_dec(v___x_2394_);
    v_lctx_2396_ = lean_ctor_get(v___y_2387_, 2);
    v_options_2397_ = lean_ctor_get(v___y_2389_, 2);
    lean_inc_ref(v_options_2397_);
    lean_inc_ref(v_lctx_2396_);
    v___x_2398_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2398_, 0, v_env_2393_);
    lean_ctor_set(v___x_2398_, 1, v_mctx_2395_);
    lean_ctor_set(v___x_2398_, 2, v_lctx_2396_);
    lean_ctor_set(v___x_2398_, 3, v_options_2397_);
    v___x_2399_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2399_, 0, v___x_2398_);
    lean_ctor_set(v___x_2399_, 1, v_msgData_2386_);
    v___x_2400_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2400_, 0, v___x_2399_);
    return v___x_2400_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2___boxed(
    mut v_msgData_2401_: *mut LeanObject,
    mut v___y_2402_: *mut LeanObject,
    mut v___y_2403_: *mut LeanObject,
    mut v___y_2404_: *mut LeanObject,
    mut v___y_2405_: *mut LeanObject,
    mut v___y_2406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2407_: *mut LeanObject = core::ptr::null_mut();
    v_res_2407_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msgData_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
    lean_dec(v___y_2405_);
    lean_dec_ref(v___y_2404_);
    lean_dec(v___y_2403_);
    lean_dec_ref(v___y_2402_);
    return v_res_2407_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(
    mut v_msg_2408_: *mut LeanObject,
    mut v___y_2409_: *mut LeanObject,
    mut v___y_2410_: *mut LeanObject,
    mut v___y_2411_: *mut LeanObject,
    mut v___y_2412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2419_: u8 = 0;
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2424_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2414_ = lean_ctor_get(v___y_2411_, 5);
                v___x_2415_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msg_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
                v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
                v_isSharedCheck_2424_ = (!lean_is_exclusive(v___x_2415_)) as u8;
                if v_isSharedCheck_2424_ == 0 {
                    v___x_2418_ = v___x_2415_;
                    v_isShared_2419_ = v_isSharedCheck_2424_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2416_);
                    lean_dec(v___x_2415_);
                    v___x_2418_ = lean_box(0);
                    v_isShared_2419_ = v_isSharedCheck_2424_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2414_);
                v___x_2420_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2420_, 0, v_ref_2414_);
                lean_ctor_set(v___x_2420_, 1, v_a_2416_);
                if v_isShared_2419_ == 0 {
                    lean_ctor_set_tag(v___x_2418_, 1);
                    lean_ctor_set(v___x_2418_, 0, v___x_2420_);
                    v___x_2422_ = v___x_2418_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
                    v___x_2422_ = v_reuseFailAlloc_2423_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2422_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg___boxed(
    mut v_msg_2425_: *mut LeanObject,
    mut v___y_2426_: *mut LeanObject,
    mut v___y_2427_: *mut LeanObject,
    mut v___y_2428_: *mut LeanObject,
    mut v___y_2429_: *mut LeanObject,
    mut v___y_2430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2431_: *mut LeanObject = core::ptr::null_mut();
    v_res_2431_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v_msg_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
    lean_dec(v___y_2429_);
    lean_dec_ref(v___y_2428_);
    lean_dec(v___y_2427_);
    lean_dec_ref(v___y_2426_);
    return v_res_2431_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1()
-> *mut LeanObject {
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    v___x_2433_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__0;
    v___x_2434_ = l_Lean_stringToMessageData(v___x_2433_);
    return v___x_2434_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(
    mut v___y_2435_: *mut LeanObject,
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
) -> *mut LeanObject {
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2451_: u8 = 0;
    let mut v_ltFn_x3f_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2459_: u8 = 0;
    let mut v_a_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2463_: u8 = 0;
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2447_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v___y_2435_,
                    v___y_2436_,
                    v___y_2437_,
                    v___y_2438_,
                    v___y_2439_,
                    v___y_2440_,
                    v___y_2441_,
                    v___y_2442_,
                    v___y_2443_,
                    v___y_2444_,
                    v___y_2445_,
                );
                if lean_obj_tag(v___x_2447_) == 0 {
                    v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
                    v_isSharedCheck_2459_ = (!lean_is_exclusive(v___x_2447_)) as u8;
                    if v_isSharedCheck_2459_ == 0 {
                        v___x_2450_ = v___x_2447_;
                        v_isShared_2451_ = v_isSharedCheck_2459_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2448_);
                        lean_dec(v___x_2447_);
                        v___x_2450_ = lean_box(0);
                        v_isShared_2451_ = v_isSharedCheck_2459_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2460_ = lean_ctor_get(v___x_2447_, 0);
                    v_isSharedCheck_2467_ = (!lean_is_exclusive(v___x_2447_)) as u8;
                    if v_isSharedCheck_2467_ == 0 {
                        v___x_2462_ = v___x_2447_;
                        v_isShared_2463_ = v_isSharedCheck_2467_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2460_);
                        lean_dec(v___x_2447_);
                        v___x_2462_ = lean_box(0);
                        v_isShared_2463_ = v_isSharedCheck_2467_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_ltFn_x3f_2452_ = lean_ctor_get(v_a_2448_, 21);
                lean_inc(v_ltFn_x3f_2452_);
                lean_dec(v_a_2448_);
                if lean_obj_tag(v_ltFn_x3f_2452_) == 1 {
                    v_val_2453_ = lean_ctor_get(v_ltFn_x3f_2452_, 0);
                    lean_inc(v_val_2453_);
                    lean_dec_ref_known(v_ltFn_x3f_2452_, 1);
                    if v_isShared_2451_ == 0 {
                        lean_ctor_set(v___x_2450_, 0, v_val_2453_);
                        v___x_2455_ = v___x_2450_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_val_2453_);
                        v___x_2455_ = v_reuseFailAlloc_2456_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_ltFn_x3f_2452_);
                    lean_del_object(v___x_2450_);
                    v___x_2457_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1_once), _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1);
                    v___x_2458_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v___x_2457_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
                    return v___x_2458_;
                }
            }
            2 => {
                return v___x_2455_;
            }
            3 => {
                if v_isShared_2463_ == 0 {
                    v___x_2465_ = v___x_2462_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
                    v___x_2465_ = v_reuseFailAlloc_2466_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2465_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___boxed(
    mut v___y_2468_: *mut LeanObject,
    mut v___y_2469_: *mut LeanObject,
    mut v___y_2470_: *mut LeanObject,
    mut v___y_2471_: *mut LeanObject,
    mut v___y_2472_: *mut LeanObject,
    mut v___y_2473_: *mut LeanObject,
    mut v___y_2474_: *mut LeanObject,
    mut v___y_2475_: *mut LeanObject,
    mut v___y_2476_: *mut LeanObject,
    mut v___y_2477_: *mut LeanObject,
    mut v___y_2478_: *mut LeanObject,
    mut v___y_2479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2480_: *mut LeanObject = core::ptr::null_mut();
    v_res_2480_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
    lean_dec(v___y_2478_);
    lean_dec_ref(v___y_2477_);
    lean_dec(v___y_2476_);
    lean_dec_ref(v___y_2475_);
    lean_dec(v___y_2474_);
    lean_dec_ref(v___y_2473_);
    lean_dec(v___y_2472_);
    lean_dec_ref(v___y_2471_);
    lean_dec(v___y_2470_);
    lean_dec(v___y_2469_);
    lean_dec(v___y_2468_);
    return v_res_2480_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    v___x_2482_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__0;
    v___x_2483_ = l_Lean_stringToMessageData(v___x_2482_);
    return v___x_2483_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(
    mut v___y_2484_: *mut LeanObject,
    mut v___y_2485_: *mut LeanObject,
    mut v___y_2486_: *mut LeanObject,
    mut v___y_2487_: *mut LeanObject,
    mut v___y_2488_: *mut LeanObject,
    mut v___y_2489_: *mut LeanObject,
    mut v___y_2490_: *mut LeanObject,
    mut v___y_2491_: *mut LeanObject,
    mut v___y_2492_: *mut LeanObject,
    mut v___y_2493_: *mut LeanObject,
    mut v___y_2494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2500_: u8 = 0;
    let mut v_leFn_x3f_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2508_: u8 = 0;
    let mut v_a_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2512_: u8 = 0;
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2516_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2496_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v___y_2484_,
                    v___y_2485_,
                    v___y_2486_,
                    v___y_2487_,
                    v___y_2488_,
                    v___y_2489_,
                    v___y_2490_,
                    v___y_2491_,
                    v___y_2492_,
                    v___y_2493_,
                    v___y_2494_,
                );
                if lean_obj_tag(v___x_2496_) == 0 {
                    v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
                    v_isSharedCheck_2508_ = (!lean_is_exclusive(v___x_2496_)) as u8;
                    if v_isSharedCheck_2508_ == 0 {
                        v___x_2499_ = v___x_2496_;
                        v_isShared_2500_ = v_isSharedCheck_2508_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2497_);
                        lean_dec(v___x_2496_);
                        v___x_2499_ = lean_box(0);
                        v_isShared_2500_ = v_isSharedCheck_2508_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2509_ = lean_ctor_get(v___x_2496_, 0);
                    v_isSharedCheck_2516_ = (!lean_is_exclusive(v___x_2496_)) as u8;
                    if v_isSharedCheck_2516_ == 0 {
                        v___x_2511_ = v___x_2496_;
                        v_isShared_2512_ = v_isSharedCheck_2516_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2509_);
                        lean_dec(v___x_2496_);
                        v___x_2511_ = lean_box(0);
                        v_isShared_2512_ = v_isSharedCheck_2516_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_leFn_x3f_2501_ = lean_ctor_get(v_a_2497_, 20);
                lean_inc(v_leFn_x3f_2501_);
                lean_dec(v_a_2497_);
                if lean_obj_tag(v_leFn_x3f_2501_) == 1 {
                    v_val_2502_ = lean_ctor_get(v_leFn_x3f_2501_, 0);
                    lean_inc(v_val_2502_);
                    lean_dec_ref_known(v_leFn_x3f_2501_, 1);
                    if v_isShared_2500_ == 0 {
                        lean_ctor_set(v___x_2499_, 0, v_val_2502_);
                        v___x_2504_ = v___x_2499_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_val_2502_);
                        v___x_2504_ = v_reuseFailAlloc_2505_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_leFn_x3f_2501_);
                    lean_del_object(v___x_2499_);
                    v___x_2506_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1);
                    v___x_2507_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v___x_2506_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
                    return v___x_2507_;
                }
            }
            2 => {
                return v___x_2504_;
            }
            3 => {
                if v_isShared_2512_ == 0 {
                    v___x_2514_ = v___x_2511_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
                    v___x_2514_ = v_reuseFailAlloc_2515_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2514_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___boxed(
    mut v___y_2517_: *mut LeanObject,
    mut v___y_2518_: *mut LeanObject,
    mut v___y_2519_: *mut LeanObject,
    mut v___y_2520_: *mut LeanObject,
    mut v___y_2521_: *mut LeanObject,
    mut v___y_2522_: *mut LeanObject,
    mut v___y_2523_: *mut LeanObject,
    mut v___y_2524_: *mut LeanObject,
    mut v___y_2525_: *mut LeanObject,
    mut v___y_2526_: *mut LeanObject,
    mut v___y_2527_: *mut LeanObject,
    mut v___y_2528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2529_: *mut LeanObject = core::ptr::null_mut();
    v_res_2529_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
    lean_dec(v___y_2527_);
    lean_dec_ref(v___y_2526_);
    lean_dec(v___y_2525_);
    lean_dec_ref(v___y_2524_);
    lean_dec(v___y_2523_);
    lean_dec_ref(v___y_2522_);
    lean_dec(v___y_2521_);
    lean_dec_ref(v___y_2520_);
    lean_dec(v___y_2519_);
    lean_dec(v___y_2518_);
    lean_dec(v___y_2517_);
    return v_res_2529_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(
    mut v_p_2530_: *mut LeanObject,
    mut v_strict_2531_: u8,
    mut v___y_2532_: *mut LeanObject,
    mut v___y_2533_: *mut LeanObject,
    mut v___y_2534_: *mut LeanObject,
    mut v___y_2535_: *mut LeanObject,
    mut v___y_2536_: *mut LeanObject,
    mut v___y_2537_: *mut LeanObject,
    mut v___y_2538_: *mut LeanObject,
    mut v___y_2539_: *mut LeanObject,
    mut v___y_2540_: *mut LeanObject,
    mut v___y_2541_: *mut LeanObject,
    mut v___y_2542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2552_: u8 = 0;
    let mut v_ofNatZero_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2558_: u8 = 0;
    let mut v_a_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2566_: u8 = 0;
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2575_: u8 = 0;
    let mut v_ofNatZero_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2581_: u8 = 0;
    let mut v_a_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2585_: u8 = 0;
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2589_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_strict_2531_ == 0 {
                    v___x_2544_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
                    if lean_obj_tag(v___x_2544_) == 0 {
                        v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
                        lean_inc(v_a_2545_);
                        lean_dec_ref_known(v___x_2544_, 1);
                        v___x_2546_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(v_p_2530_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
                        if lean_obj_tag(v___x_2546_) == 0 {
                            v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
                            lean_inc(v_a_2547_);
                            lean_dec_ref_known(v___x_2546_, 1);
                            v___x_2548_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                                v___y_2532_,
                                v___y_2533_,
                                v___y_2534_,
                                v___y_2535_,
                                v___y_2536_,
                                v___y_2537_,
                                v___y_2538_,
                                v___y_2539_,
                                v___y_2540_,
                                v___y_2541_,
                                v___y_2542_,
                            );
                            if lean_obj_tag(v___x_2548_) == 0 {
                                v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
                                v_isSharedCheck_2558_ = (!lean_is_exclusive(v___x_2548_)) as u8;
                                if v_isSharedCheck_2558_ == 0 {
                                    v___x_2551_ = v___x_2548_;
                                    v_isShared_2552_ = v_isSharedCheck_2558_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_2549_);
                                    lean_dec(v___x_2548_);
                                    v___x_2551_ = lean_box(0);
                                    v_isShared_2552_ = v_isSharedCheck_2558_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_2547_);
                                lean_dec(v_a_2545_);
                                v_a_2559_ = lean_ctor_get(v___x_2548_, 0);
                                v_isSharedCheck_2566_ = (!lean_is_exclusive(v___x_2548_)) as u8;
                                if v_isSharedCheck_2566_ == 0 {
                                    v___x_2561_ = v___x_2548_;
                                    v_isShared_2562_ = v_isSharedCheck_2566_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_2559_);
                                    lean_dec(v___x_2548_);
                                    v___x_2561_ = lean_box(0);
                                    v_isShared_2562_ = v_isSharedCheck_2566_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_2545_);
                            return v___x_2546_;
                        }
                    } else {
                        return v___x_2544_;
                    }
                } else {
                    v___x_2567_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
                    if lean_obj_tag(v___x_2567_) == 0 {
                        v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
                        lean_inc(v_a_2568_);
                        lean_dec_ref_known(v___x_2567_, 1);
                        v___x_2569_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(v_p_2530_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
                        if lean_obj_tag(v___x_2569_) == 0 {
                            v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
                            lean_inc(v_a_2570_);
                            lean_dec_ref_known(v___x_2569_, 1);
                            v___x_2571_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                                v___y_2532_,
                                v___y_2533_,
                                v___y_2534_,
                                v___y_2535_,
                                v___y_2536_,
                                v___y_2537_,
                                v___y_2538_,
                                v___y_2539_,
                                v___y_2540_,
                                v___y_2541_,
                                v___y_2542_,
                            );
                            if lean_obj_tag(v___x_2571_) == 0 {
                                v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
                                v_isSharedCheck_2581_ = (!lean_is_exclusive(v___x_2571_)) as u8;
                                if v_isSharedCheck_2581_ == 0 {
                                    v___x_2574_ = v___x_2571_;
                                    v_isShared_2575_ = v_isSharedCheck_2581_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_2572_);
                                    lean_dec(v___x_2571_);
                                    v___x_2574_ = lean_box(0);
                                    v_isShared_2575_ = v_isSharedCheck_2581_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_2570_);
                                lean_dec(v_a_2568_);
                                v_a_2582_ = lean_ctor_get(v___x_2571_, 0);
                                v_isSharedCheck_2589_ = (!lean_is_exclusive(v___x_2571_)) as u8;
                                if v_isSharedCheck_2589_ == 0 {
                                    v___x_2584_ = v___x_2571_;
                                    v_isShared_2585_ = v_isSharedCheck_2589_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_2582_);
                                    lean_dec(v___x_2571_);
                                    v___x_2584_ = lean_box(0);
                                    v_isShared_2585_ = v_isSharedCheck_2589_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_2568_);
                            return v___x_2569_;
                        }
                    } else {
                        return v___x_2567_;
                    }
                }
            }
            1 => {
                v_ofNatZero_2553_ = lean_ctor_get(v_a_2549_, 18);
                lean_inc_ref(v_ofNatZero_2553_);
                lean_dec(v_a_2549_);
                v___x_2554_ = l_Lean_mkAppB(v_a_2545_, v_a_2547_, v_ofNatZero_2553_);
                if v_isShared_2552_ == 0 {
                    lean_ctor_set(v___x_2551_, 0, v___x_2554_);
                    v___x_2556_ = v___x_2551_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
                    v___x_2556_ = v_reuseFailAlloc_2557_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2556_;
            }
            3 => {
                if v_isShared_2562_ == 0 {
                    v___x_2564_ = v___x_2561_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
                    v___x_2564_ = v_reuseFailAlloc_2565_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2564_;
            }
            5 => {
                v_ofNatZero_2576_ = lean_ctor_get(v_a_2572_, 18);
                lean_inc_ref(v_ofNatZero_2576_);
                lean_dec(v_a_2572_);
                v___x_2577_ = l_Lean_mkAppB(v_a_2568_, v_a_2570_, v_ofNatZero_2576_);
                if v_isShared_2575_ == 0 {
                    lean_ctor_set(v___x_2574_, 0, v___x_2577_);
                    v___x_2579_ = v___x_2574_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2577_);
                    v___x_2579_ = v_reuseFailAlloc_2580_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2579_;
            }
            7 => {
                if v_isShared_2585_ == 0 {
                    v___x_2587_ = v___x_2584_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
                    v___x_2587_ = v_reuseFailAlloc_2588_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2587_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0___boxed(
    mut v_p_2590_: *mut LeanObject,
    mut v_strict_2591_: *mut LeanObject,
    mut v___y_2592_: *mut LeanObject,
    mut v___y_2593_: *mut LeanObject,
    mut v___y_2594_: *mut LeanObject,
    mut v___y_2595_: *mut LeanObject,
    mut v___y_2596_: *mut LeanObject,
    mut v___y_2597_: *mut LeanObject,
    mut v___y_2598_: *mut LeanObject,
    mut v___y_2599_: *mut LeanObject,
    mut v___y_2600_: *mut LeanObject,
    mut v___y_2601_: *mut LeanObject,
    mut v___y_2602_: *mut LeanObject,
    mut v___y_2603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_strict_boxed_2604_: u8 = 0;
    let mut v_res_2605_: *mut LeanObject = core::ptr::null_mut();
    v_strict_boxed_2604_ = (lean_unbox(v_strict_2591_) as u8);
    v_res_2605_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(v_p_2590_, v_strict_boxed_2604_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
    lean_dec(v___y_2602_);
    lean_dec_ref(v___y_2601_);
    lean_dec(v___y_2600_);
    lean_dec_ref(v___y_2599_);
    lean_dec(v___y_2598_);
    lean_dec_ref(v___y_2597_);
    lean_dec(v___y_2596_);
    lean_dec_ref(v___y_2595_);
    lean_dec(v___y_2594_);
    lean_dec(v___y_2593_);
    lean_dec(v___y_2592_);
    lean_dec(v_p_2590_);
    return v_res_2605_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(
    mut v_c_2606_: *mut LeanObject,
    mut v___y_2607_: *mut LeanObject,
    mut v___y_2608_: *mut LeanObject,
    mut v___y_2609_: *mut LeanObject,
    mut v___y_2610_: *mut LeanObject,
    mut v___y_2611_: *mut LeanObject,
    mut v___y_2612_: *mut LeanObject,
    mut v___y_2613_: *mut LeanObject,
    mut v___y_2614_: *mut LeanObject,
    mut v___y_2615_: *mut LeanObject,
    mut v___y_2616_: *mut LeanObject,
    mut v___y_2617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_2620_: u8 = 0;
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    v_p_2619_ = lean_ctor_get(v_c_2606_, 0);
    v_strict_2620_ = lean_ctor_get_uint8(
        v_c_2606_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    v___x_2621_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(v_p_2619_, v_strict_2620_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
    return v___x_2621_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___boxed(
    mut v_c_2622_: *mut LeanObject,
    mut v___y_2623_: *mut LeanObject,
    mut v___y_2624_: *mut LeanObject,
    mut v___y_2625_: *mut LeanObject,
    mut v___y_2626_: *mut LeanObject,
    mut v___y_2627_: *mut LeanObject,
    mut v___y_2628_: *mut LeanObject,
    mut v___y_2629_: *mut LeanObject,
    mut v___y_2630_: *mut LeanObject,
    mut v___y_2631_: *mut LeanObject,
    mut v___y_2632_: *mut LeanObject,
    mut v___y_2633_: *mut LeanObject,
    mut v___y_2634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2635_: *mut LeanObject = core::ptr::null_mut();
    v_res_2635_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
    lean_dec(v___y_2633_);
    lean_dec_ref(v___y_2632_);
    lean_dec(v___y_2631_);
    lean_dec_ref(v___y_2630_);
    lean_dec(v___y_2629_);
    lean_dec_ref(v___y_2628_);
    lean_dec(v___y_2627_);
    lean_dec_ref(v___y_2626_);
    lean_dec(v___y_2625_);
    lean_dec(v___y_2624_);
    lean_dec(v___y_2623_);
    lean_dec_ref(v_c_2622_);
    return v_res_2635_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0()
-> f64 {
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: f64 = 0.0;
    v___x_2636_ = lean_unsigned_to_nat(0);
    v___x_2637_ = lean_float_of_nat(v___x_2636_);
    return v___x_2637_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(
    mut v_cls_2641_: *mut LeanObject,
    mut v_msg_2642_: *mut LeanObject,
    mut v___y_2643_: *mut LeanObject,
    mut v___y_2644_: *mut LeanObject,
    mut v___y_2645_: *mut LeanObject,
    mut v___y_2646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2653_: u8 = 0;
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2666_: u8 = 0;
    let mut v_tid_2667_: u64 = 0;
    let mut v_traces_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2671_: u8 = 0;
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: f64 = 0.0;
    let mut v___x_2674_: u8 = 0;
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2692_: u8 = 0;
    let mut v_isSharedCheck_2693_: u8 = 0;
    let mut v_isSharedCheck_2694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2648_ = lean_ctor_get(v___y_2645_, 5);
                v___x_2649_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msg_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
                v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
                v_isSharedCheck_2694_ = (!lean_is_exclusive(v___x_2649_)) as u8;
                if v_isSharedCheck_2694_ == 0 {
                    v___x_2652_ = v___x_2649_;
                    v_isShared_2653_ = v_isSharedCheck_2694_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2650_);
                    lean_dec(v___x_2649_);
                    v___x_2652_ = lean_box(0);
                    v_isShared_2653_ = v_isSharedCheck_2694_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2654_ = lean_st_ref_take(v___y_2646_);
                v_traceState_2655_ = lean_ctor_get(v___x_2654_, 4);
                v_env_2656_ = lean_ctor_get(v___x_2654_, 0);
                v_nextMacroScope_2657_ = lean_ctor_get(v___x_2654_, 1);
                v_ngen_2658_ = lean_ctor_get(v___x_2654_, 2);
                v_auxDeclNGen_2659_ = lean_ctor_get(v___x_2654_, 3);
                v_cache_2660_ = lean_ctor_get(v___x_2654_, 5);
                v_messages_2661_ = lean_ctor_get(v___x_2654_, 6);
                v_infoState_2662_ = lean_ctor_get(v___x_2654_, 7);
                v_snapshotTasks_2663_ = lean_ctor_get(v___x_2654_, 8);
                v_isSharedCheck_2693_ = (!lean_is_exclusive(v___x_2654_)) as u8;
                if v_isSharedCheck_2693_ == 0 {
                    v___x_2665_ = v___x_2654_;
                    v_isShared_2666_ = v_isSharedCheck_2693_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2663_);
                    lean_inc(v_infoState_2662_);
                    lean_inc(v_messages_2661_);
                    lean_inc(v_cache_2660_);
                    lean_inc(v_traceState_2655_);
                    lean_inc(v_auxDeclNGen_2659_);
                    lean_inc(v_ngen_2658_);
                    lean_inc(v_nextMacroScope_2657_);
                    lean_inc(v_env_2656_);
                    lean_dec(v___x_2654_);
                    v___x_2665_ = lean_box(0);
                    v_isShared_2666_ = v_isSharedCheck_2693_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2667_ = lean_ctor_get_uint64(
                    v_traceState_2655_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_2668_ = lean_ctor_get(v_traceState_2655_, 0);
                v_isSharedCheck_2692_ = (!lean_is_exclusive(v_traceState_2655_)) as u8;
                if v_isSharedCheck_2692_ == 0 {
                    v___x_2670_ = v_traceState_2655_;
                    v_isShared_2671_ = v_isSharedCheck_2692_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_2668_);
                    lean_dec(v_traceState_2655_);
                    v___x_2670_ = lean_box(0);
                    v_isShared_2671_ = v_isSharedCheck_2692_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2672_ = lean_box(0);
                v___x_2673_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0);
                v___x_2674_ = 0;
                v___x_2675_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__1;
                v___x_2676_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_2676_, 0, v_cls_2641_);
                lean_ctor_set(v___x_2676_, 1, v___x_2672_);
                lean_ctor_set(v___x_2676_, 2, v___x_2675_);
                lean_ctor_set_float(
                    v___x_2676_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2673_,
                );
                lean_ctor_set_float(
                    v___x_2676_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_2673_,
                );
                lean_ctor_set_uint8(
                    v___x_2676_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_2674_,
                );
                v___x_2677_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__2;
                v___x_2678_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_2678_, 0, v___x_2676_);
                lean_ctor_set(v___x_2678_, 1, v_a_2650_);
                lean_ctor_set(v___x_2678_, 2, v___x_2677_);
                lean_inc(v_ref_2648_);
                v___x_2679_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2679_, 0, v_ref_2648_);
                lean_ctor_set(v___x_2679_, 1, v___x_2678_);
                v___x_2680_ = l_Lean_PersistentArray_push___redArg(v_traces_2668_, v___x_2679_);
                if v_isShared_2671_ == 0 {
                    lean_ctor_set(v___x_2670_, 0, v___x_2680_);
                    v___x_2682_ = v___x_2670_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2680_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2691_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2667_,
                    );
                    v___x_2682_ = v_reuseFailAlloc_2691_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2666_ == 0 {
                    lean_ctor_set(v___x_2665_, 4, v___x_2682_);
                    v___x_2684_ = v___x_2665_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_env_2656_);
                    lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_nextMacroScope_2657_);
                    lean_ctor_set(v_reuseFailAlloc_2690_, 2, v_ngen_2658_);
                    lean_ctor_set(v_reuseFailAlloc_2690_, 3, v_auxDeclNGen_2659_);
                    lean_ctor_set(v_reuseFailAlloc_2690_, 4, v___x_2682_);
                    lean_ctor_set(v_reuseFailAlloc_2690_, 5, v_cache_2660_);
                    lean_ctor_set(v_reuseFailAlloc_2690_, 6, v_messages_2661_);
                    lean_ctor_set(v_reuseFailAlloc_2690_, 7, v_infoState_2662_);
                    lean_ctor_set(v_reuseFailAlloc_2690_, 8, v_snapshotTasks_2663_);
                    v___x_2684_ = v_reuseFailAlloc_2690_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2685_ = lean_st_ref_set(v___y_2646_, v___x_2684_);
                v___x_2686_ = lean_box(0);
                if v_isShared_2653_ == 0 {
                    lean_ctor_set(v___x_2652_, 0, v___x_2686_);
                    v___x_2688_ = v___x_2652_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2686_);
                    v___x_2688_ = v_reuseFailAlloc_2689_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2688_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___boxed(
    mut v_cls_2695_: *mut LeanObject,
    mut v_msg_2696_: *mut LeanObject,
    mut v___y_2697_: *mut LeanObject,
    mut v___y_2698_: *mut LeanObject,
    mut v___y_2699_: *mut LeanObject,
    mut v___y_2700_: *mut LeanObject,
    mut v___y_2701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2702_: *mut LeanObject = core::ptr::null_mut();
    v_res_2702_ =
        l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(
            v_cls_2695_,
            v_msg_2696_,
            v___y_2697_,
            v___y_2698_,
            v___y_2699_,
            v___y_2700_,
        );
    lean_dec(v___y_2700_);
    lean_dec_ref(v___y_2699_);
    lean_dec(v___y_2698_);
    lean_dec_ref(v___y_2697_);
    return v_res_2702_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0() -> *mut LeanObject
{
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    v___x_2703_ = lean_unsigned_to_nat(0);
    v___x_2704_ = lean_nat_to_int(v___x_2703_);
    return v___x_2704_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8() -> *mut LeanObject
{
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    v___x_2716_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5;
    v___x_2717_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7;
    v___x_2718_ = l_Lean_Name_append(v___x_2717_, v___x_2716_);
    return v___x_2718_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11() -> *mut LeanObject
{
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    v___x_2724_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10;
    v___x_2725_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7;
    v___x_2726_ = l_Lean_Name_append(v___x_2725_, v___x_2724_);
    return v___x_2726_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14() -> *mut LeanObject
{
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    v___x_2733_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13;
    v___x_2734_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7;
    v___x_2735_ = l_Lean_Name_append(v___x_2734_, v___x_2733_);
    return v___x_2735_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16() -> *mut LeanObject
{
    let mut v_cls_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    v_cls_2740_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15;
    v___x_2741_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7;
    v___x_2742_ = l_Lean_Name_append(v___x_2741_, v_cls_2740_);
    return v___x_2742_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(
    mut v_c_2743_: *mut LeanObject,
    mut v_a_2744_: *mut LeanObject,
    mut v_a_2745_: *mut LeanObject,
    mut v_a_2746_: *mut LeanObject,
    mut v_a_2747_: *mut LeanObject,
    mut v_a_2748_: *mut LeanObject,
    mut v_a_2749_: *mut LeanObject,
    mut v_a_2750_: *mut LeanObject,
    mut v_a_2751_: *mut LeanObject,
    mut v_a_2752_: *mut LeanObject,
    mut v_a_2753_: *mut LeanObject,
    mut v_a_2754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2790_: u8 = 0;
    let mut v___x_2791_: u8 = 0;
    let mut v___x_2792_: u8 = 0;
    let mut v___x_2793_: u8 = 0;
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2799_: u8 = 0;
    let mut v_a_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2803_: u8 = 0;
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2807_: u8 = 0;
    let mut v___y_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: u8 = 0;
    let mut v___f_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2835_: u8 = 0;
    let mut v___y_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_2849_: u8 = 0;
    let mut v_options_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2851_: u8 = 0;
    let mut v_inheritedTraceOptions_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: u8 = 0;
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2863_: u8 = 0;
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2867_: u8 = 0;
    let mut v_options_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2869_: u8 = 0;
    let mut v_inheritedTraceOptions_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: u8 = 0;
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2881_: u8 = 0;
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2885_: u8 = 0;
    let mut v_options_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2887_: u8 = 0;
    let mut v_k_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: u8 = 0;
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2903_: u8 = 0;
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2907_: u8 = 0;
    let mut v_cls_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: u8 = 0;
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2918_: u8 = 0;
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2922_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2833_ = lean_ctor_get(v_a_2753_, 2);
                v_inheritedTraceOptions_2834_ = lean_ctor_get(v_a_2753_, 13);
                v_hasTrace_2835_ = lean_ctor_get_uint8(
                    v_options_2833_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_2835_ == 0 {
                    v___y_2837_ = v_a_2744_;
                    v___y_2838_ = v_a_2745_;
                    v___y_2839_ = v_a_2746_;
                    v___y_2840_ = v_a_2747_;
                    v___y_2841_ = v_a_2748_;
                    v___y_2842_ = v_a_2749_;
                    v___y_2843_ = v_a_2750_;
                    v___y_2844_ = v_a_2751_;
                    v___y_2845_ = v_a_2752_;
                    v___y_2846_ = v_a_2753_;
                    v___y_2847_ = v_a_2754_;
                    state = 9;
                    continue;
                } else {
                    v_cls_2908_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15;
                    v___x_2909_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16,
                    );
                    v___x_2910_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_2834_,
                        v_options_2833_,
                        v___x_2909_,
                    );
                    if v___x_2910_ == 0 {
                        v___y_2837_ = v_a_2744_;
                        v___y_2838_ = v_a_2745_;
                        v___y_2839_ = v_a_2746_;
                        v___y_2840_ = v_a_2747_;
                        v___y_2841_ = v_a_2748_;
                        v___y_2842_ = v_a_2749_;
                        v___y_2843_ = v_a_2750_;
                        v___y_2844_ = v_a_2751_;
                        v___y_2845_ = v_a_2752_;
                        v___y_2846_ = v_a_2753_;
                        v___y_2847_ = v_a_2754_;
                        state = 9;
                        continue;
                    } else {
                        v___x_2911_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
                        if lean_obj_tag(v___x_2911_) == 0 {
                            v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
                            lean_inc(v_a_2912_);
                            lean_dec_ref_known(v___x_2911_, 1);
                            v___x_2913_ = l_Lean_MessageData_ofExpr(v_a_2912_);
                            v___x_2914_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_2908_, v___x_2913_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
                            if lean_obj_tag(v___x_2914_) == 0 {
                                lean_dec_ref_known(v___x_2914_, 1);
                                v___y_2837_ = v_a_2744_;
                                v___y_2838_ = v_a_2745_;
                                v___y_2839_ = v_a_2746_;
                                v___y_2840_ = v_a_2747_;
                                v___y_2841_ = v_a_2748_;
                                v___y_2842_ = v_a_2749_;
                                v___y_2843_ = v_a_2750_;
                                v___y_2844_ = v_a_2751_;
                                v___y_2845_ = v_a_2752_;
                                v___y_2846_ = v_a_2753_;
                                v___y_2847_ = v_a_2754_;
                                state = 9;
                                continue;
                            } else {
                                lean_dec_ref(v_c_2743_);
                                return v___x_2914_;
                            }
                        } else {
                            lean_dec_ref(v_c_2743_);
                            v_a_2915_ = lean_ctor_get(v___x_2911_, 0);
                            v_isSharedCheck_2922_ = (!lean_is_exclusive(v___x_2911_)) as u8;
                            if v_isSharedCheck_2922_ == 0 {
                                v___x_2917_ = v___x_2911_;
                                v_isShared_2918_ = v_isSharedCheck_2922_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_a_2915_);
                                lean_dec(v___x_2911_);
                                v___x_2917_ = lean_box(0);
                                v_isShared_2918_ = v_isSharedCheck_2922_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2757_ = lean_box(0);
                v___x_2758_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2758_, 0, v___x_2757_);
                return v___x_2758_;
            }
            2 => {
                v___x_2771_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2771_, 0, v_c_2743_);
                v___x_2772_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(
                    v___x_2771_,
                    v___y_2760_,
                    v___y_2761_,
                    v___y_2762_,
                    v___y_2763_,
                    v___y_2764_,
                    v___y_2765_,
                    v___y_2766_,
                    v___y_2767_,
                    v___y_2768_,
                    v___y_2769_,
                    v___y_2770_,
                );
                return v___x_2772_;
            }
            3 => {
                v___x_2786_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(
                    v_c_2743_,
                    v___y_2775_,
                    v___y_2776_,
                    v___y_2777_,
                    v___y_2778_,
                    v___y_2779_,
                    v___y_2780_,
                    v___y_2781_,
                    v___y_2782_,
                    v___y_2783_,
                    v___y_2784_,
                    v___y_2785_,
                );
                if lean_obj_tag(v___x_2786_) == 0 {
                    v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
                    v_isSharedCheck_2799_ = (!lean_is_exclusive(v___x_2786_)) as u8;
                    if v_isSharedCheck_2799_ == 0 {
                        v___x_2789_ = v___x_2786_;
                        v_isShared_2790_ = v_isSharedCheck_2799_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2787_);
                        lean_dec(v___x_2786_);
                        v___x_2789_ = lean_box(0);
                        v_isShared_2790_ = v_isSharedCheck_2799_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___y_2774_);
                    v_a_2800_ = lean_ctor_get(v___x_2786_, 0);
                    v_isSharedCheck_2807_ = (!lean_is_exclusive(v___x_2786_)) as u8;
                    if v_isSharedCheck_2807_ == 0 {
                        v___x_2802_ = v___x_2786_;
                        v_isShared_2803_ = v_isSharedCheck_2807_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2800_);
                        lean_dec(v___x_2786_);
                        v___x_2802_ = lean_box(0);
                        v_isShared_2803_ = v_isSharedCheck_2807_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2791_ = 0;
                v___x_2792_ = (lean_unbox(v_a_2787_) as u8);
                lean_dec(v_a_2787_);
                v___x_2793_ = l_Lean_instBEqLBool_beq(v___x_2792_, v___x_2791_);
                if v___x_2793_ == 0 {
                    lean_dec(v___y_2774_);
                    v___x_2794_ = lean_box(0);
                    if v_isShared_2790_ == 0 {
                        lean_ctor_set(v___x_2789_, 0, v___x_2794_);
                        v___x_2796_ = v___x_2789_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
                        v___x_2796_ = v_reuseFailAlloc_2797_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2789_);
                    v___x_2798_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(
                        v___y_2774_,
                        v___y_2775_,
                        v___y_2776_,
                    );
                    return v___x_2798_;
                }
            }
            5 => {
                return v___x_2796_;
            }
            6 => {
                if v_isShared_2803_ == 0 {
                    v___x_2805_ = v___x_2802_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
                    v___x_2805_ = v_reuseFailAlloc_2806_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2805_;
            }
            8 => {
                v___x_2824_ = l_Lean_Grind_Linarith_Poly_updateOccs(
                    v___y_2810_,
                    v___y_2813_,
                    v___y_2814_,
                    v___y_2815_,
                    v___y_2816_,
                    v___y_2817_,
                    v___y_2818_,
                    v___y_2819_,
                    v___y_2820_,
                    v___y_2821_,
                    v___y_2822_,
                    v___y_2823_,
                );
                if lean_obj_tag(v___x_2824_) == 0 {
                    lean_dec_ref_known(v___x_2824_, 1);
                    v___x_2825_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0,
                    );
                    v___x_2826_ = lean_int_dec_lt(v___y_2812_, v___x_2825_);
                    lean_dec(v___y_2812_);
                    if v___x_2826_ == 0 {
                        lean_inc_ref(v_c_2743_);
                        lean_inc(v___y_2813_);
                        v___f_2827_ = lean_alloc_closure(
                            l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        lean_closure_set(v___f_2827_, 0, v___y_2813_);
                        lean_closure_set(v___f_2827_, 1, v_c_2743_);
                        lean_closure_set(v___f_2827_, 2, v___y_2809_);
                        v___x_2828_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                        v___x_2829_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2828_, v___f_2827_, v___y_2814_);
                        if lean_obj_tag(v___x_2829_) == 0 {
                            lean_dec_ref_known(v___x_2829_, 1);
                            v___y_2774_ = v___y_2811_;
                            v___y_2775_ = v___y_2813_;
                            v___y_2776_ = v___y_2814_;
                            v___y_2777_ = v___y_2815_;
                            v___y_2778_ = v___y_2816_;
                            v___y_2779_ = v___y_2817_;
                            v___y_2780_ = v___y_2818_;
                            v___y_2781_ = v___y_2819_;
                            v___y_2782_ = v___y_2820_;
                            v___y_2783_ = v___y_2821_;
                            v___y_2784_ = v___y_2822_;
                            v___y_2785_ = v___y_2823_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___y_2811_);
                            lean_dec_ref(v_c_2743_);
                            return v___x_2829_;
                        }
                    } else {
                        lean_inc_ref(v_c_2743_);
                        lean_inc(v___y_2813_);
                        v___f_2830_ = lean_alloc_closure(
                            l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        lean_closure_set(v___f_2830_, 0, v___y_2813_);
                        lean_closure_set(v___f_2830_, 1, v_c_2743_);
                        lean_closure_set(v___f_2830_, 2, v___y_2809_);
                        v___x_2831_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                        v___x_2832_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2831_, v___f_2830_, v___y_2814_);
                        if lean_obj_tag(v___x_2832_) == 0 {
                            lean_dec_ref_known(v___x_2832_, 1);
                            v___y_2774_ = v___y_2811_;
                            v___y_2775_ = v___y_2813_;
                            v___y_2776_ = v___y_2814_;
                            v___y_2777_ = v___y_2815_;
                            v___y_2778_ = v___y_2816_;
                            v___y_2779_ = v___y_2817_;
                            v___y_2780_ = v___y_2818_;
                            v___y_2781_ = v___y_2819_;
                            v___y_2782_ = v___y_2820_;
                            v___y_2783_ = v___y_2821_;
                            v___y_2784_ = v___y_2822_;
                            v___y_2785_ = v___y_2823_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___y_2811_);
                            lean_dec_ref(v_c_2743_);
                            return v___x_2832_;
                        }
                    }
                } else {
                    lean_dec(v___y_2812_);
                    lean_dec(v___y_2811_);
                    lean_dec(v___y_2809_);
                    lean_dec_ref(v_c_2743_);
                    return v___x_2824_;
                }
            }
            9 => {
                v_p_2848_ = lean_ctor_get(v_c_2743_, 0);
                if lean_obj_tag(v_p_2848_) == 0 {
                    v_strict_2849_ = lean_ctor_get_uint8(
                        v_c_2743_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    if v_strict_2849_ == 0 {
                        v_options_2850_ = lean_ctor_get(v___y_2846_, 2);
                        v_hasTrace_2851_ = lean_ctor_get_uint8(
                            v_options_2850_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_2851_ == 0 {
                            lean_dec_ref(v_c_2743_);
                            state = 1;
                            continue;
                        } else {
                            v_inheritedTraceOptions_2852_ = lean_ctor_get(v___y_2846_, 13);
                            v___x_2853_ =
                                l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5;
                            v___x_2854_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8_once), _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8);
                            v___x_2855_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_2852_,
                                v_options_2850_,
                                v___x_2854_,
                            );
                            if v___x_2855_ == 0 {
                                lean_dec_ref(v_c_2743_);
                                state = 1;
                                continue;
                            } else {
                                v___x_2856_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_2743_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
                                lean_dec_ref(v_c_2743_);
                                if lean_obj_tag(v___x_2856_) == 0 {
                                    v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
                                    lean_inc(v_a_2857_);
                                    lean_dec_ref_known(v___x_2856_, 1);
                                    v___x_2858_ = l_Lean_MessageData_ofExpr(v_a_2857_);
                                    v___x_2859_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_2853_, v___x_2858_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
                                    return v___x_2859_;
                                } else {
                                    v_a_2860_ = lean_ctor_get(v___x_2856_, 0);
                                    v_isSharedCheck_2867_ = (!lean_is_exclusive(v___x_2856_)) as u8;
                                    if v_isSharedCheck_2867_ == 0 {
                                        v___x_2862_ = v___x_2856_;
                                        v_isShared_2863_ = v_isSharedCheck_2867_;
                                        state = 10;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2860_);
                                        lean_dec(v___x_2856_);
                                        v___x_2862_ = lean_box(0);
                                        v_isShared_2863_ = v_isSharedCheck_2867_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        v_options_2868_ = lean_ctor_get(v___y_2846_, 2);
                        v_hasTrace_2869_ = lean_ctor_get_uint8(
                            v_options_2868_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_2869_ == 0 {
                            v___y_2760_ = v___y_2837_;
                            v___y_2761_ = v___y_2838_;
                            v___y_2762_ = v___y_2839_;
                            v___y_2763_ = v___y_2840_;
                            v___y_2764_ = v___y_2841_;
                            v___y_2765_ = v___y_2842_;
                            v___y_2766_ = v___y_2843_;
                            v___y_2767_ = v___y_2844_;
                            v___y_2768_ = v___y_2845_;
                            v___y_2769_ = v___y_2846_;
                            v___y_2770_ = v___y_2847_;
                            state = 2;
                            continue;
                        } else {
                            v_inheritedTraceOptions_2870_ = lean_ctor_get(v___y_2846_, 13);
                            v___x_2871_ =
                                l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10;
                            v___x_2872_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11_once), _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11);
                            v___x_2873_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_2870_,
                                v_options_2868_,
                                v___x_2872_,
                            );
                            if v___x_2873_ == 0 {
                                v___y_2760_ = v___y_2837_;
                                v___y_2761_ = v___y_2838_;
                                v___y_2762_ = v___y_2839_;
                                v___y_2763_ = v___y_2840_;
                                v___y_2764_ = v___y_2841_;
                                v___y_2765_ = v___y_2842_;
                                v___y_2766_ = v___y_2843_;
                                v___y_2767_ = v___y_2844_;
                                v___y_2768_ = v___y_2845_;
                                v___y_2769_ = v___y_2846_;
                                v___y_2770_ = v___y_2847_;
                                state = 2;
                                continue;
                            } else {
                                v___x_2874_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_2743_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
                                if lean_obj_tag(v___x_2874_) == 0 {
                                    v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
                                    lean_inc(v_a_2875_);
                                    lean_dec_ref_known(v___x_2874_, 1);
                                    v___x_2876_ = l_Lean_MessageData_ofExpr(v_a_2875_);
                                    v___x_2877_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_2871_, v___x_2876_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
                                    if lean_obj_tag(v___x_2877_) == 0 {
                                        lean_dec_ref_known(v___x_2877_, 1);
                                        v___y_2760_ = v___y_2837_;
                                        v___y_2761_ = v___y_2838_;
                                        v___y_2762_ = v___y_2839_;
                                        v___y_2763_ = v___y_2840_;
                                        v___y_2764_ = v___y_2841_;
                                        v___y_2765_ = v___y_2842_;
                                        v___y_2766_ = v___y_2843_;
                                        v___y_2767_ = v___y_2844_;
                                        v___y_2768_ = v___y_2845_;
                                        v___y_2769_ = v___y_2846_;
                                        v___y_2770_ = v___y_2847_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec_ref(v_c_2743_);
                                        return v___x_2877_;
                                    }
                                } else {
                                    lean_dec_ref(v_c_2743_);
                                    v_a_2878_ = lean_ctor_get(v___x_2874_, 0);
                                    v_isSharedCheck_2885_ = (!lean_is_exclusive(v___x_2874_)) as u8;
                                    if v_isSharedCheck_2885_ == 0 {
                                        v___x_2880_ = v___x_2874_;
                                        v_isShared_2881_ = v_isSharedCheck_2885_;
                                        state = 12;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2878_);
                                        lean_dec(v___x_2874_);
                                        v___x_2880_ = lean_box(0);
                                        v_isShared_2881_ = v_isSharedCheck_2885_;
                                        state = 12;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    v_options_2886_ = lean_ctor_get(v___y_2846_, 2);
                    v_hasTrace_2887_ = lean_ctor_get_uint8(
                        v_options_2886_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2887_ == 0 {
                        v_k_2888_ = lean_ctor_get(v_p_2848_, 0);
                        v_v_2889_ = lean_ctor_get(v_p_2848_, 1);
                        lean_inc(v_k_2888_);
                        lean_inc_ref(v_p_2848_);
                        lean_inc_n(v_v_2889_, 2);
                        v___y_2809_ = v_v_2889_;
                        v___y_2810_ = v_p_2848_;
                        v___y_2811_ = v_v_2889_;
                        v___y_2812_ = v_k_2888_;
                        v___y_2813_ = v___y_2837_;
                        v___y_2814_ = v___y_2838_;
                        v___y_2815_ = v___y_2839_;
                        v___y_2816_ = v___y_2840_;
                        v___y_2817_ = v___y_2841_;
                        v___y_2818_ = v___y_2842_;
                        v___y_2819_ = v___y_2843_;
                        v___y_2820_ = v___y_2844_;
                        v___y_2821_ = v___y_2845_;
                        v___y_2822_ = v___y_2846_;
                        v___y_2823_ = v___y_2847_;
                        state = 8;
                        continue;
                    } else {
                        v_k_2890_ = lean_ctor_get(v_p_2848_, 0);
                        v_v_2891_ = lean_ctor_get(v_p_2848_, 1);
                        v_inheritedTraceOptions_2892_ = lean_ctor_get(v___y_2846_, 13);
                        v___x_2893_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13;
                        v___x_2894_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14,
                        );
                        v___x_2895_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_2892_,
                            v_options_2886_,
                            v___x_2894_,
                        );
                        if v___x_2895_ == 0 {
                            lean_inc(v_k_2890_);
                            lean_inc_ref(v_p_2848_);
                            lean_inc_n(v_v_2891_, 2);
                            v___y_2809_ = v_v_2891_;
                            v___y_2810_ = v_p_2848_;
                            v___y_2811_ = v_v_2891_;
                            v___y_2812_ = v_k_2890_;
                            v___y_2813_ = v___y_2837_;
                            v___y_2814_ = v___y_2838_;
                            v___y_2815_ = v___y_2839_;
                            v___y_2816_ = v___y_2840_;
                            v___y_2817_ = v___y_2841_;
                            v___y_2818_ = v___y_2842_;
                            v___y_2819_ = v___y_2843_;
                            v___y_2820_ = v___y_2844_;
                            v___y_2821_ = v___y_2845_;
                            v___y_2822_ = v___y_2846_;
                            v___y_2823_ = v___y_2847_;
                            state = 8;
                            continue;
                        } else {
                            v___x_2896_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_2743_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
                            if lean_obj_tag(v___x_2896_) == 0 {
                                v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
                                lean_inc(v_a_2897_);
                                lean_dec_ref_known(v___x_2896_, 1);
                                v___x_2898_ = l_Lean_MessageData_ofExpr(v_a_2897_);
                                v___x_2899_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_2893_, v___x_2898_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
                                if lean_obj_tag(v___x_2899_) == 0 {
                                    lean_dec_ref_known(v___x_2899_, 1);
                                    lean_inc(v_k_2890_);
                                    lean_inc_ref(v_p_2848_);
                                    lean_inc_n(v_v_2891_, 2);
                                    v___y_2809_ = v_v_2891_;
                                    v___y_2810_ = v_p_2848_;
                                    v___y_2811_ = v_v_2891_;
                                    v___y_2812_ = v_k_2890_;
                                    v___y_2813_ = v___y_2837_;
                                    v___y_2814_ = v___y_2838_;
                                    v___y_2815_ = v___y_2839_;
                                    v___y_2816_ = v___y_2840_;
                                    v___y_2817_ = v___y_2841_;
                                    v___y_2818_ = v___y_2842_;
                                    v___y_2819_ = v___y_2843_;
                                    v___y_2820_ = v___y_2844_;
                                    v___y_2821_ = v___y_2845_;
                                    v___y_2822_ = v___y_2846_;
                                    v___y_2823_ = v___y_2847_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_dec_ref(v_c_2743_);
                                    return v___x_2899_;
                                }
                            } else {
                                lean_dec_ref(v_c_2743_);
                                v_a_2900_ = lean_ctor_get(v___x_2896_, 0);
                                v_isSharedCheck_2907_ = (!lean_is_exclusive(v___x_2896_)) as u8;
                                if v_isSharedCheck_2907_ == 0 {
                                    v___x_2902_ = v___x_2896_;
                                    v_isShared_2903_ = v_isSharedCheck_2907_;
                                    state = 14;
                                    continue;
                                } else {
                                    lean_inc(v_a_2900_);
                                    lean_dec(v___x_2896_);
                                    v___x_2902_ = lean_box(0);
                                    v_isShared_2903_ = v_isSharedCheck_2907_;
                                    state = 14;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            10 => {
                if v_isShared_2863_ == 0 {
                    v___x_2865_ = v___x_2862_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
                    v___x_2865_ = v_reuseFailAlloc_2866_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2865_;
            }
            12 => {
                if v_isShared_2881_ == 0 {
                    v___x_2883_ = v___x_2880_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
                    v___x_2883_ = v_reuseFailAlloc_2884_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2883_;
            }
            14 => {
                if v_isShared_2903_ == 0 {
                    v___x_2905_ = v___x_2902_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
                    v___x_2905_ = v_reuseFailAlloc_2906_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2905_;
            }
            16 => {
                if v_isShared_2918_ == 0 {
                    v___x_2920_ = v___x_2917_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
                    v___x_2920_ = v_reuseFailAlloc_2921_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2920_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___boxed(
    mut v_c_2923_: *mut LeanObject,
    mut v_a_2924_: *mut LeanObject,
    mut v_a_2925_: *mut LeanObject,
    mut v_a_2926_: *mut LeanObject,
    mut v_a_2927_: *mut LeanObject,
    mut v_a_2928_: *mut LeanObject,
    mut v_a_2929_: *mut LeanObject,
    mut v_a_2930_: *mut LeanObject,
    mut v_a_2931_: *mut LeanObject,
    mut v_a_2932_: *mut LeanObject,
    mut v_a_2933_: *mut LeanObject,
    mut v_a_2934_: *mut LeanObject,
    mut v_a_2935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2936_: *mut LeanObject = core::ptr::null_mut();
    v_res_2936_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(
        v_c_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_,
        v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_,
    );
    lean_dec(v_a_2934_);
    lean_dec_ref(v_a_2933_);
    lean_dec(v_a_2932_);
    lean_dec_ref(v_a_2931_);
    lean_dec(v_a_2930_);
    lean_dec_ref(v_a_2929_);
    lean_dec(v_a_2928_);
    lean_dec_ref(v_a_2927_);
    lean_dec(v_a_2926_);
    lean_dec(v_a_2925_);
    lean_dec(v_a_2924_);
    return v_res_2936_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(
    mut v_cls_2937_: *mut LeanObject,
    mut v_msg_2938_: *mut LeanObject,
    mut v___y_2939_: *mut LeanObject,
    mut v___y_2940_: *mut LeanObject,
    mut v___y_2941_: *mut LeanObject,
    mut v___y_2942_: *mut LeanObject,
    mut v___y_2943_: *mut LeanObject,
    mut v___y_2944_: *mut LeanObject,
    mut v___y_2945_: *mut LeanObject,
    mut v___y_2946_: *mut LeanObject,
    mut v___y_2947_: *mut LeanObject,
    mut v___y_2948_: *mut LeanObject,
    mut v___y_2949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    v___x_2951_ =
        l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(
            v_cls_2937_,
            v_msg_2938_,
            v___y_2946_,
            v___y_2947_,
            v___y_2948_,
            v___y_2949_,
        );
    return v___x_2951_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___boxed(
    mut v_cls_2952_: *mut LeanObject,
    mut v_msg_2953_: *mut LeanObject,
    mut v___y_2954_: *mut LeanObject,
    mut v___y_2955_: *mut LeanObject,
    mut v___y_2956_: *mut LeanObject,
    mut v___y_2957_: *mut LeanObject,
    mut v___y_2958_: *mut LeanObject,
    mut v___y_2959_: *mut LeanObject,
    mut v___y_2960_: *mut LeanObject,
    mut v___y_2961_: *mut LeanObject,
    mut v___y_2962_: *mut LeanObject,
    mut v___y_2963_: *mut LeanObject,
    mut v___y_2964_: *mut LeanObject,
    mut v___y_2965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2966_: *mut LeanObject = core::ptr::null_mut();
    v_res_2966_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(
        v_cls_2952_,
        v_msg_2953_,
        v___y_2954_,
        v___y_2955_,
        v___y_2956_,
        v___y_2957_,
        v___y_2958_,
        v___y_2959_,
        v___y_2960_,
        v___y_2961_,
        v___y_2962_,
        v___y_2963_,
        v___y_2964_,
    );
    lean_dec(v___y_2964_);
    lean_dec_ref(v___y_2963_);
    lean_dec(v___y_2962_);
    lean_dec_ref(v___y_2961_);
    lean_dec(v___y_2960_);
    lean_dec_ref(v___y_2959_);
    lean_dec(v___y_2958_);
    lean_dec_ref(v___y_2957_);
    lean_dec(v___y_2956_);
    lean_dec(v___y_2955_);
    lean_dec(v___y_2954_);
    return v_res_2966_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5(
    mut v_00_u03b1_2967_: *mut LeanObject,
    mut v_msg_2968_: *mut LeanObject,
    mut v___y_2969_: *mut LeanObject,
    mut v___y_2970_: *mut LeanObject,
    mut v___y_2971_: *mut LeanObject,
    mut v___y_2972_: *mut LeanObject,
    mut v___y_2973_: *mut LeanObject,
    mut v___y_2974_: *mut LeanObject,
    mut v___y_2975_: *mut LeanObject,
    mut v___y_2976_: *mut LeanObject,
    mut v___y_2977_: *mut LeanObject,
    mut v___y_2978_: *mut LeanObject,
    mut v___y_2979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    v___x_2981_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v_msg_2968_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
    return v___x_2981_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___boxed(
    mut v_00_u03b1_2982_: *mut LeanObject,
    mut v_msg_2983_: *mut LeanObject,
    mut v___y_2984_: *mut LeanObject,
    mut v___y_2985_: *mut LeanObject,
    mut v___y_2986_: *mut LeanObject,
    mut v___y_2987_: *mut LeanObject,
    mut v___y_2988_: *mut LeanObject,
    mut v___y_2989_: *mut LeanObject,
    mut v___y_2990_: *mut LeanObject,
    mut v___y_2991_: *mut LeanObject,
    mut v___y_2992_: *mut LeanObject,
    mut v___y_2993_: *mut LeanObject,
    mut v___y_2994_: *mut LeanObject,
    mut v___y_2995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2996_: *mut LeanObject = core::ptr::null_mut();
    v_res_2996_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5(v_00_u03b1_2982_, v_msg_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
    lean_dec(v___y_2994_);
    lean_dec_ref(v___y_2993_);
    lean_dec(v___y_2992_);
    lean_dec_ref(v___y_2991_);
    lean_dec(v___y_2990_);
    lean_dec_ref(v___y_2989_);
    lean_dec(v___y_2988_);
    lean_dec_ref(v___y_2987_);
    lean_dec(v___y_2986_);
    lean_dec(v___y_2985_);
    lean_dec(v___y_2984_);
    return v_res_2996_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(
    mut v_a_2997_: *mut LeanObject,
    mut v_e_2998_: *mut LeanObject,
    mut v_s_2999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_structs_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_forbiddenNatModules_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natStructs_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natTypeIdOf_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNatStructId_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: u8 = 0;
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3012_: u8 = 0;
    let mut v_v_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringId_x3f_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intModuleInst_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leInst_x3f_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltInst_x3f_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lawfulOrderLTInst_x3f_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isPreorderInst_x3f_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_orderedAddInst_x3f_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isLinearInst_x3f_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_noNatDivInst_x3f_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_x3f_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_x3f_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_orderedRingInst_x3f_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofNatZero_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leFn_x3f_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltFn_x3f_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zsmulFn_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nsmulFn_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zsmulFn_x3f_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nsmulFn_x3f_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_homomulFn_x3f_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowers_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uppers_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_3050_: u8 = 0;
    let mut v_conflict_x3f_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_occurs_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ignored_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3059_: u8 = 0;
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3070_: u8 = 0;
    let mut v_isSharedCheck_3071_: u8 = 0;
    let mut v_unused_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_3000_ = lean_ctor_get(v_s_2999_, 0);
                v_typeIdOf_3001_ = lean_ctor_get(v_s_2999_, 1);
                v_exprToStructId_3002_ = lean_ctor_get(v_s_2999_, 2);
                v_exprToStructIdEntries_3003_ = lean_ctor_get(v_s_2999_, 3);
                v_forbiddenNatModules_3004_ = lean_ctor_get(v_s_2999_, 4);
                v_natStructs_3005_ = lean_ctor_get(v_s_2999_, 5);
                v_natTypeIdOf_3006_ = lean_ctor_get(v_s_2999_, 6);
                v_exprToNatStructId_3007_ = lean_ctor_get(v_s_2999_, 7);
                v___x_3008_ = lean_array_get_size(v_structs_3000_);
                v___x_3009_ = lean_nat_dec_lt(v_a_2997_, v___x_3008_);
                if v___x_3009_ == 0 {
                    lean_dec_ref(v_e_2998_);
                    return v_s_2999_;
                } else {
                    lean_inc_ref(v_exprToNatStructId_3007_);
                    lean_inc_ref(v_natTypeIdOf_3006_);
                    lean_inc_ref(v_natStructs_3005_);
                    lean_inc_ref(v_forbiddenNatModules_3004_);
                    lean_inc_ref(v_exprToStructIdEntries_3003_);
                    lean_inc_ref(v_exprToStructId_3002_);
                    lean_inc_ref(v_typeIdOf_3001_);
                    lean_inc_ref(v_structs_3000_);
                    v_isSharedCheck_3071_ = (!lean_is_exclusive(v_s_2999_)) as u8;
                    if v_isSharedCheck_3071_ == 0 {
                        v_unused_3072_ = lean_ctor_get(v_s_2999_, 7);
                        lean_dec(v_unused_3072_);
                        v_unused_3073_ = lean_ctor_get(v_s_2999_, 6);
                        lean_dec(v_unused_3073_);
                        v_unused_3074_ = lean_ctor_get(v_s_2999_, 5);
                        lean_dec(v_unused_3074_);
                        v_unused_3075_ = lean_ctor_get(v_s_2999_, 4);
                        lean_dec(v_unused_3075_);
                        v_unused_3076_ = lean_ctor_get(v_s_2999_, 3);
                        lean_dec(v_unused_3076_);
                        v_unused_3077_ = lean_ctor_get(v_s_2999_, 2);
                        lean_dec(v_unused_3077_);
                        v_unused_3078_ = lean_ctor_get(v_s_2999_, 1);
                        lean_dec(v_unused_3078_);
                        v_unused_3079_ = lean_ctor_get(v_s_2999_, 0);
                        lean_dec(v_unused_3079_);
                        v___x_3011_ = v_s_2999_;
                        v_isShared_3012_ = v_isSharedCheck_3071_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_s_2999_);
                        v___x_3011_ = lean_box(0);
                        v_isShared_3012_ = v_isSharedCheck_3071_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3013_ = lean_array_fget(v_structs_3000_, v_a_2997_);
                v_id_3014_ = lean_ctor_get(v_v_3013_, 0);
                v_ringId_x3f_3015_ = lean_ctor_get(v_v_3013_, 1);
                v_type_3016_ = lean_ctor_get(v_v_3013_, 2);
                v_u_3017_ = lean_ctor_get(v_v_3013_, 3);
                v_intModuleInst_3018_ = lean_ctor_get(v_v_3013_, 4);
                v_leInst_x3f_3019_ = lean_ctor_get(v_v_3013_, 5);
                v_ltInst_x3f_3020_ = lean_ctor_get(v_v_3013_, 6);
                v_lawfulOrderLTInst_x3f_3021_ = lean_ctor_get(v_v_3013_, 7);
                v_isPreorderInst_x3f_3022_ = lean_ctor_get(v_v_3013_, 8);
                v_orderedAddInst_x3f_3023_ = lean_ctor_get(v_v_3013_, 9);
                v_isLinearInst_x3f_3024_ = lean_ctor_get(v_v_3013_, 10);
                v_noNatDivInst_x3f_3025_ = lean_ctor_get(v_v_3013_, 11);
                v_ringInst_x3f_3026_ = lean_ctor_get(v_v_3013_, 12);
                v_commRingInst_x3f_3027_ = lean_ctor_get(v_v_3013_, 13);
                v_orderedRingInst_x3f_3028_ = lean_ctor_get(v_v_3013_, 14);
                v_fieldInst_x3f_3029_ = lean_ctor_get(v_v_3013_, 15);
                v_charInst_x3f_3030_ = lean_ctor_get(v_v_3013_, 16);
                v_zero_3031_ = lean_ctor_get(v_v_3013_, 17);
                v_ofNatZero_3032_ = lean_ctor_get(v_v_3013_, 18);
                v_one_x3f_3033_ = lean_ctor_get(v_v_3013_, 19);
                v_leFn_x3f_3034_ = lean_ctor_get(v_v_3013_, 20);
                v_ltFn_x3f_3035_ = lean_ctor_get(v_v_3013_, 21);
                v_addFn_3036_ = lean_ctor_get(v_v_3013_, 22);
                v_zsmulFn_3037_ = lean_ctor_get(v_v_3013_, 23);
                v_nsmulFn_3038_ = lean_ctor_get(v_v_3013_, 24);
                v_zsmulFn_x3f_3039_ = lean_ctor_get(v_v_3013_, 25);
                v_nsmulFn_x3f_3040_ = lean_ctor_get(v_v_3013_, 26);
                v_homomulFn_x3f_3041_ = lean_ctor_get(v_v_3013_, 27);
                v_subFn_3042_ = lean_ctor_get(v_v_3013_, 28);
                v_negFn_3043_ = lean_ctor_get(v_v_3013_, 29);
                v_vars_3044_ = lean_ctor_get(v_v_3013_, 30);
                v_varMap_3045_ = lean_ctor_get(v_v_3013_, 31);
                v_lowers_3046_ = lean_ctor_get(v_v_3013_, 32);
                v_uppers_3047_ = lean_ctor_get(v_v_3013_, 33);
                v_diseqs_3048_ = lean_ctor_get(v_v_3013_, 34);
                v_assignment_3049_ = lean_ctor_get(v_v_3013_, 35);
                v_caseSplits_3050_ = lean_ctor_get_uint8(
                    v_v_3013_,
                    (core::mem::size_of::<*mut LeanObject>() * 42) as u32,
                );
                v_conflict_x3f_3051_ = lean_ctor_get(v_v_3013_, 36);
                v_diseqSplits_3052_ = lean_ctor_get(v_v_3013_, 37);
                v_elimEqs_3053_ = lean_ctor_get(v_v_3013_, 38);
                v_elimStack_3054_ = lean_ctor_get(v_v_3013_, 39);
                v_occurs_3055_ = lean_ctor_get(v_v_3013_, 40);
                v_ignored_3056_ = lean_ctor_get(v_v_3013_, 41);
                v_isSharedCheck_3070_ = (!lean_is_exclusive(v_v_3013_)) as u8;
                if v_isSharedCheck_3070_ == 0 {
                    v___x_3058_ = v_v_3013_;
                    v_isShared_3059_ = v_isSharedCheck_3070_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_ignored_3056_);
                    lean_inc(v_occurs_3055_);
                    lean_inc(v_elimStack_3054_);
                    lean_inc(v_elimEqs_3053_);
                    lean_inc(v_diseqSplits_3052_);
                    lean_inc(v_conflict_x3f_3051_);
                    lean_inc(v_assignment_3049_);
                    lean_inc(v_diseqs_3048_);
                    lean_inc(v_uppers_3047_);
                    lean_inc(v_lowers_3046_);
                    lean_inc(v_varMap_3045_);
                    lean_inc(v_vars_3044_);
                    lean_inc(v_negFn_3043_);
                    lean_inc(v_subFn_3042_);
                    lean_inc(v_homomulFn_x3f_3041_);
                    lean_inc(v_nsmulFn_x3f_3040_);
                    lean_inc(v_zsmulFn_x3f_3039_);
                    lean_inc(v_nsmulFn_3038_);
                    lean_inc(v_zsmulFn_3037_);
                    lean_inc(v_addFn_3036_);
                    lean_inc(v_ltFn_x3f_3035_);
                    lean_inc(v_leFn_x3f_3034_);
                    lean_inc(v_one_x3f_3033_);
                    lean_inc(v_ofNatZero_3032_);
                    lean_inc(v_zero_3031_);
                    lean_inc(v_charInst_x3f_3030_);
                    lean_inc(v_fieldInst_x3f_3029_);
                    lean_inc(v_orderedRingInst_x3f_3028_);
                    lean_inc(v_commRingInst_x3f_3027_);
                    lean_inc(v_ringInst_x3f_3026_);
                    lean_inc(v_noNatDivInst_x3f_3025_);
                    lean_inc(v_isLinearInst_x3f_3024_);
                    lean_inc(v_orderedAddInst_x3f_3023_);
                    lean_inc(v_isPreorderInst_x3f_3022_);
                    lean_inc(v_lawfulOrderLTInst_x3f_3021_);
                    lean_inc(v_ltInst_x3f_3020_);
                    lean_inc(v_leInst_x3f_3019_);
                    lean_inc(v_intModuleInst_3018_);
                    lean_inc(v_u_3017_);
                    lean_inc(v_type_3016_);
                    lean_inc(v_ringId_x3f_3015_);
                    lean_inc(v_id_3014_);
                    lean_dec(v_v_3013_);
                    v___x_3058_ = lean_box(0);
                    v_isShared_3059_ = v_isSharedCheck_3070_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3060_ = lean_box(0);
                v_xs_x27_3061_ = lean_array_fset(v_structs_3000_, v_a_2997_, v___x_3060_);
                v___x_3062_ = l_Lean_PersistentArray_push___redArg(v_ignored_3056_, v_e_2998_);
                if v_isShared_3059_ == 0 {
                    lean_ctor_set(v___x_3058_, 41, v___x_3062_);
                    v___x_3064_ = v___x_3058_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 42, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_id_3014_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 1, v_ringId_x3f_3015_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 2, v_type_3016_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 3, v_u_3017_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 4, v_intModuleInst_3018_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 5, v_leInst_x3f_3019_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 6, v_ltInst_x3f_3020_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 7, v_lawfulOrderLTInst_x3f_3021_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 8, v_isPreorderInst_x3f_3022_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 9, v_orderedAddInst_x3f_3023_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 10, v_isLinearInst_x3f_3024_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 11, v_noNatDivInst_x3f_3025_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 12, v_ringInst_x3f_3026_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 13, v_commRingInst_x3f_3027_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 14, v_orderedRingInst_x3f_3028_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 15, v_fieldInst_x3f_3029_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 16, v_charInst_x3f_3030_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 17, v_zero_3031_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 18, v_ofNatZero_3032_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 19, v_one_x3f_3033_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 20, v_leFn_x3f_3034_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 21, v_ltFn_x3f_3035_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 22, v_addFn_3036_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 23, v_zsmulFn_3037_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 24, v_nsmulFn_3038_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 25, v_zsmulFn_x3f_3039_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 26, v_nsmulFn_x3f_3040_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 27, v_homomulFn_x3f_3041_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 28, v_subFn_3042_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 29, v_negFn_3043_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 30, v_vars_3044_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 31, v_varMap_3045_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 32, v_lowers_3046_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 33, v_uppers_3047_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 34, v_diseqs_3048_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 35, v_assignment_3049_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 36, v_conflict_x3f_3051_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 37, v_diseqSplits_3052_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 38, v_elimEqs_3053_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 39, v_elimStack_3054_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 40, v_occurs_3055_);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 41, v___x_3062_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3069_,
                        (core::mem::size_of::<*mut LeanObject>() * 42) as u32,
                        v_caseSplits_3050_,
                    );
                    v___x_3064_ = v_reuseFailAlloc_3069_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3065_ = lean_array_fset(v_xs_x27_3061_, v_a_2997_, v___x_3064_);
                if v_isShared_3012_ == 0 {
                    lean_ctor_set(v___x_3011_, 0, v___x_3065_);
                    v___x_3067_ = v___x_3011_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3065_);
                    lean_ctor_set(v_reuseFailAlloc_3068_, 1, v_typeIdOf_3001_);
                    lean_ctor_set(v_reuseFailAlloc_3068_, 2, v_exprToStructId_3002_);
                    lean_ctor_set(v_reuseFailAlloc_3068_, 3, v_exprToStructIdEntries_3003_);
                    lean_ctor_set(v_reuseFailAlloc_3068_, 4, v_forbiddenNatModules_3004_);
                    lean_ctor_set(v_reuseFailAlloc_3068_, 5, v_natStructs_3005_);
                    lean_ctor_set(v_reuseFailAlloc_3068_, 6, v_natTypeIdOf_3006_);
                    lean_ctor_set(v_reuseFailAlloc_3068_, 7, v_exprToNatStructId_3007_);
                    v___x_3067_ = v_reuseFailAlloc_3068_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3067_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed(
    mut v_a_3080_: *mut LeanObject,
    mut v_e_3081_: *mut LeanObject,
    mut v_s_3082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3083_: *mut LeanObject = core::ptr::null_mut();
    v_res_3083_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(v_a_3080_, v_e_3081_, v_s_3082_);
    lean_dec(v_a_3080_);
    return v_res_3083_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(
    mut v_e_3084_: *mut LeanObject,
    mut v_lhs_3085_: *mut LeanObject,
    mut v_rhs_3086_: *mut LeanObject,
    mut v_strict_3087_: u8,
    mut v_eqTrue_3088_: u8,
    mut v_a_3089_: *mut LeanObject,
    mut v_a_3090_: *mut LeanObject,
    mut v_a_3091_: *mut LeanObject,
    mut v_a_3092_: *mut LeanObject,
    mut v_a_3093_: *mut LeanObject,
    mut v_a_3094_: *mut LeanObject,
    mut v_a_3095_: *mut LeanObject,
    mut v_a_3096_: *mut LeanObject,
    mut v_a_3097_: *mut LeanObject,
    mut v_a_3098_: *mut LeanObject,
    mut v_a_3099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3101_: u8 = 0;
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3109_: u8 = 0;
    let mut v_val_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3117_: u8 = 0;
    let mut v_val_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: u8 = 0;
    let mut v___f_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3130_: u8 = 0;
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3142_: u8 = 0;
    let mut v_val_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3152_: u8 = 0;
    let mut v_a_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3156_: u8 = 0;
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3160_: u8 = 0;
    let mut v_a_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3164_: u8 = 0;
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3168_: u8 = 0;
    let mut v_a_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3176_: u8 = 0;
    let mut v___x_3177_: u8 = 0;
    let mut v_a_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3181_: u8 = 0;
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3185_: u8 = 0;
    let mut v_a_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3200_: u8 = 0;
    let mut v_val_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3210_: u8 = 0;
    let mut v_a_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3214_: u8 = 0;
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3218_: u8 = 0;
    let mut v_a_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3222_: u8 = 0;
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3226_: u8 = 0;
    let mut v_a_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3230_: u8 = 0;
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3234_: u8 = 0;
    let mut v_a_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3238_: u8 = 0;
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3242_: u8 = 0;
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3247_: u8 = 0;
    let mut v_a_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3251_: u8 = 0;
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3255_: u8 = 0;
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3260_: u8 = 0;
    let mut v_a_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3264_: u8 = 0;
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3268_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3101_ = 0;
                v___x_3102_ = lean_unsigned_to_nat(0);
                v___x_3103_ = lean_box((v___x_3101_) as usize);
                v___x_3104_ = lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed as *mut core::ffi::c_void,
                    15,
                    3,
                );
                lean_closure_set(v___x_3104_, 0, v_lhs_3085_);
                lean_closure_set(v___x_3104_, 1, v___x_3103_);
                lean_closure_set(v___x_3104_, 2, v___x_3102_);
                v___x_3105_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(
                    v___x_3104_,
                    v_a_3089_,
                    v_a_3090_,
                    v_a_3091_,
                    v_a_3092_,
                    v_a_3093_,
                    v_a_3094_,
                    v_a_3095_,
                    v_a_3096_,
                    v_a_3097_,
                    v_a_3098_,
                    v_a_3099_,
                );
                if lean_obj_tag(v___x_3105_) == 0 {
                    v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
                    v_isSharedCheck_3260_ = (!lean_is_exclusive(v___x_3105_)) as u8;
                    if v_isSharedCheck_3260_ == 0 {
                        v___x_3108_ = v___x_3105_;
                        v_isShared_3109_ = v_isSharedCheck_3260_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3106_);
                        lean_dec(v___x_3105_);
                        v___x_3108_ = lean_box(0);
                        v_isShared_3109_ = v_isSharedCheck_3260_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_rhs_3086_);
                    lean_dec_ref(v_e_3084_);
                    v_a_3261_ = lean_ctor_get(v___x_3105_, 0);
                    v_isSharedCheck_3268_ = (!lean_is_exclusive(v___x_3105_)) as u8;
                    if v_isSharedCheck_3268_ == 0 {
                        v___x_3263_ = v___x_3105_;
                        v_isShared_3264_ = v_isSharedCheck_3268_;
                        state = 28;
                        continue;
                    } else {
                        lean_inc(v_a_3261_);
                        lean_dec(v___x_3105_);
                        v___x_3263_ = lean_box(0);
                        v_isShared_3264_ = v_isSharedCheck_3268_;
                        state = 28;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3106_) == 1 {
                    lean_del_object(v___x_3108_);
                    v_val_3110_ = lean_ctor_get(v_a_3106_, 0);
                    lean_inc(v_val_3110_);
                    lean_dec_ref_known(v_a_3106_, 1);
                    v___x_3111_ = lean_box((v___x_3101_) as usize);
                    v___x_3112_ = lean_alloc_closure(
                        l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed
                            as *mut core::ffi::c_void,
                        15,
                        3,
                    );
                    lean_closure_set(v___x_3112_, 0, v_rhs_3086_);
                    lean_closure_set(v___x_3112_, 1, v___x_3111_);
                    lean_closure_set(v___x_3112_, 2, v___x_3102_);
                    v___x_3113_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(
                        v___x_3112_,
                        v_a_3089_,
                        v_a_3090_,
                        v_a_3091_,
                        v_a_3092_,
                        v_a_3093_,
                        v_a_3094_,
                        v_a_3095_,
                        v_a_3096_,
                        v_a_3097_,
                        v_a_3098_,
                        v_a_3099_,
                    );
                    if lean_obj_tag(v___x_3113_) == 0 {
                        v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
                        v_isSharedCheck_3247_ = (!lean_is_exclusive(v___x_3113_)) as u8;
                        if v_isSharedCheck_3247_ == 0 {
                            v___x_3116_ = v___x_3113_;
                            v_isShared_3117_ = v_isSharedCheck_3247_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3114_);
                            lean_dec(v___x_3113_);
                            v___x_3116_ = lean_box(0);
                            v_isShared_3117_ = v_isSharedCheck_3247_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_3110_);
                        lean_dec_ref(v_e_3084_);
                        v_a_3248_ = lean_ctor_get(v___x_3113_, 0);
                        v_isSharedCheck_3255_ = (!lean_is_exclusive(v___x_3113_)) as u8;
                        if v_isSharedCheck_3255_ == 0 {
                            v___x_3250_ = v___x_3113_;
                            v_isShared_3251_ = v_isSharedCheck_3255_;
                            state = 25;
                            continue;
                        } else {
                            lean_inc(v_a_3248_);
                            lean_dec(v___x_3113_);
                            v___x_3250_ = lean_box(0);
                            v_isShared_3251_ = v_isSharedCheck_3255_;
                            state = 25;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3106_);
                    lean_dec_ref(v_rhs_3086_);
                    lean_dec_ref(v_e_3084_);
                    v___x_3256_ = lean_box(0);
                    if v_isShared_3109_ == 0 {
                        lean_ctor_set(v___x_3108_, 0, v___x_3256_);
                        v___x_3258_ = v___x_3108_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3256_);
                        v___x_3258_ = v_reuseFailAlloc_3259_;
                        state = 27;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_3114_) == 1 {
                    lean_del_object(v___x_3116_);
                    v_val_3118_ = lean_ctor_get(v_a_3114_, 0);
                    lean_inc(v_val_3118_);
                    lean_dec_ref_known(v_a_3114_, 1);
                    v___x_3119_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3084_, v_a_3090_);
                    if lean_obj_tag(v___x_3119_) == 0 {
                        if v_eqTrue_3088_ == 0 {
                            v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
                            lean_inc(v_a_3120_);
                            lean_dec_ref_known(v___x_3119_, 1);
                            v___x_3121_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(
                                v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_,
                                v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_,
                            );
                            if lean_obj_tag(v___x_3121_) == 0 {
                                v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
                                lean_inc(v_a_3122_);
                                lean_dec_ref_known(v___x_3121_, 1);
                                v___x_3123_ = (lean_unbox(v_a_3122_) as u8);
                                if v___x_3123_ == 0 {
                                    lean_dec(v_a_3122_);
                                    lean_dec(v_a_3120_);
                                    lean_dec(v_val_3118_);
                                    lean_dec(v_val_3110_);
                                    lean_inc(v_a_3089_);
                                    v___f_3124_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                                    lean_closure_set(v___f_3124_, 0, v_a_3089_);
                                    lean_closure_set(v___f_3124_, 1, v_e_3084_);
                                    v___x_3125_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                                    v___x_3126_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3125_, v___f_3124_, v_a_3090_);
                                    return v___x_3126_;
                                } else {
                                    lean_inc(v_val_3110_);
                                    lean_inc(v_val_3118_);
                                    v___x_3127_ = lean_alloc_ctor(6, 2, (0) as u32);
                                    lean_ctor_set(v___x_3127_, 0, v_val_3118_);
                                    lean_ctor_set(v___x_3127_, 1, v_val_3110_);
                                    v___x_3128_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_3127_);
                                    if v_strict_3087_ == 0 {
                                        v___x_3177_ = (lean_unbox(v_a_3122_) as u8);
                                        lean_dec(v_a_3122_);
                                        v___y_3130_ = v___x_3177_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_dec(v_a_3122_);
                                        v___y_3130_ = v_eqTrue_3088_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_3120_);
                                lean_dec(v_val_3118_);
                                lean_dec(v_val_3110_);
                                lean_dec_ref(v_e_3084_);
                                v_a_3178_ = lean_ctor_get(v___x_3121_, 0);
                                v_isSharedCheck_3185_ = (!lean_is_exclusive(v___x_3121_)) as u8;
                                if v_isSharedCheck_3185_ == 0 {
                                    v___x_3180_ = v___x_3121_;
                                    v_isShared_3181_ = v_isSharedCheck_3185_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_a_3178_);
                                    lean_dec(v___x_3121_);
                                    v___x_3180_ = lean_box(0);
                                    v_isShared_3181_ = v_isSharedCheck_3185_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            v_a_3186_ = lean_ctor_get(v___x_3119_, 0);
                            lean_inc(v_a_3186_);
                            lean_dec_ref_known(v___x_3119_, 1);
                            lean_inc(v_val_3118_);
                            lean_inc(v_val_3110_);
                            v___x_3187_ = lean_alloc_ctor(6, 2, (0) as u32);
                            lean_ctor_set(v___x_3187_, 0, v_val_3110_);
                            lean_ctor_set(v___x_3187_, 1, v_val_3118_);
                            v___x_3188_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_3187_);
                            v___x_3189_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v___x_3189_, 0, v_e_3084_);
                            lean_ctor_set(v___x_3189_, 1, v_val_3110_);
                            lean_ctor_set(v___x_3189_, 2, v_val_3118_);
                            v___x_3190_ = lean_alloc_ctor(0, 2, (1) as u32);
                            lean_ctor_set(v___x_3190_, 0, v___x_3188_);
                            lean_ctor_set(v___x_3190_, 1, v___x_3189_);
                            lean_ctor_set_uint8(
                                v___x_3190_,
                                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                                v_strict_3087_,
                            );
                            v___x_3191_ =
                                l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(
                                    v___x_3190_,
                                    v_a_3089_,
                                    v_a_3090_,
                                    v_a_3091_,
                                    v_a_3092_,
                                    v_a_3093_,
                                    v_a_3094_,
                                    v_a_3095_,
                                    v_a_3096_,
                                    v_a_3097_,
                                    v_a_3098_,
                                    v_a_3099_,
                                );
                            if lean_obj_tag(v___x_3191_) == 0 {
                                v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
                                lean_inc(v_a_3192_);
                                lean_dec_ref_known(v___x_3191_, 1);
                                v_p_3193_ = lean_ctor_get(v_a_3192_, 0);
                                lean_inc(v_a_3186_);
                                lean_inc_ref(v_p_3193_);
                                v___x_3194_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(
                                    v_p_3193_, v_a_3186_, v_a_3089_, v_a_3090_, v_a_3091_,
                                    v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_,
                                    v_a_3097_, v_a_3098_, v_a_3099_,
                                );
                                if lean_obj_tag(v___x_3194_) == 0 {
                                    v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
                                    lean_inc(v_a_3195_);
                                    lean_dec_ref_known(v___x_3194_, 1);
                                    v___x_3196_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(
                                        v_a_3195_,
                                        v___x_3101_,
                                        v_a_3186_,
                                        v_a_3089_,
                                        v_a_3090_,
                                        v_a_3091_,
                                        v_a_3092_,
                                        v_a_3093_,
                                        v_a_3094_,
                                        v_a_3095_,
                                        v_a_3096_,
                                        v_a_3097_,
                                        v_a_3098_,
                                        v_a_3099_,
                                    );
                                    if lean_obj_tag(v___x_3196_) == 0 {
                                        v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
                                        v_isSharedCheck_3210_ =
                                            (!lean_is_exclusive(v___x_3196_)) as u8;
                                        if v_isSharedCheck_3210_ == 0 {
                                            v___x_3199_ = v___x_3196_;
                                            v_isShared_3200_ = v_isSharedCheck_3210_;
                                            state = 14;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3197_);
                                            lean_dec(v___x_3196_);
                                            v___x_3199_ = lean_box(0);
                                            v_isShared_3200_ = v_isSharedCheck_3210_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_3192_);
                                        v_a_3211_ = lean_ctor_get(v___x_3196_, 0);
                                        v_isSharedCheck_3218_ =
                                            (!lean_is_exclusive(v___x_3196_)) as u8;
                                        if v_isSharedCheck_3218_ == 0 {
                                            v___x_3213_ = v___x_3196_;
                                            v_isShared_3214_ = v_isSharedCheck_3218_;
                                            state = 16;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3211_);
                                            lean_dec(v___x_3196_);
                                            v___x_3213_ = lean_box(0);
                                            v_isShared_3214_ = v_isSharedCheck_3218_;
                                            state = 16;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_3192_);
                                    lean_dec(v_a_3186_);
                                    v_a_3219_ = lean_ctor_get(v___x_3194_, 0);
                                    v_isSharedCheck_3226_ = (!lean_is_exclusive(v___x_3194_)) as u8;
                                    if v_isSharedCheck_3226_ == 0 {
                                        v___x_3221_ = v___x_3194_;
                                        v_isShared_3222_ = v_isSharedCheck_3226_;
                                        state = 18;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3219_);
                                        lean_dec(v___x_3194_);
                                        v___x_3221_ = lean_box(0);
                                        v_isShared_3222_ = v_isSharedCheck_3226_;
                                        state = 18;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_3186_);
                                v_a_3227_ = lean_ctor_get(v___x_3191_, 0);
                                v_isSharedCheck_3234_ = (!lean_is_exclusive(v___x_3191_)) as u8;
                                if v_isSharedCheck_3234_ == 0 {
                                    v___x_3229_ = v___x_3191_;
                                    v_isShared_3230_ = v_isSharedCheck_3234_;
                                    state = 20;
                                    continue;
                                } else {
                                    lean_inc(v_a_3227_);
                                    lean_dec(v___x_3191_);
                                    v___x_3229_ = lean_box(0);
                                    v_isShared_3230_ = v_isSharedCheck_3234_;
                                    state = 20;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_val_3118_);
                        lean_dec(v_val_3110_);
                        lean_dec_ref(v_e_3084_);
                        v_a_3235_ = lean_ctor_get(v___x_3119_, 0);
                        v_isSharedCheck_3242_ = (!lean_is_exclusive(v___x_3119_)) as u8;
                        if v_isSharedCheck_3242_ == 0 {
                            v___x_3237_ = v___x_3119_;
                            v_isShared_3238_ = v_isSharedCheck_3242_;
                            state = 22;
                            continue;
                        } else {
                            lean_inc(v_a_3235_);
                            lean_dec(v___x_3119_);
                            v___x_3237_ = lean_box(0);
                            v_isShared_3238_ = v_isSharedCheck_3242_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3114_);
                    lean_dec(v_val_3110_);
                    lean_dec_ref(v_e_3084_);
                    v___x_3243_ = lean_box(0);
                    if v_isShared_3117_ == 0 {
                        lean_ctor_set(v___x_3116_, 0, v___x_3243_);
                        v___x_3245_ = v___x_3116_;
                        state = 24;
                        continue;
                    } else {
                        v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3243_);
                        v___x_3245_ = v_reuseFailAlloc_3246_;
                        state = 24;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3131_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3131_, 0, v_e_3084_);
                lean_ctor_set(v___x_3131_, 1, v_val_3110_);
                lean_ctor_set(v___x_3131_, 2, v_val_3118_);
                v___x_3132_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_3132_, 0, v___x_3128_);
                lean_ctor_set(v___x_3132_, 1, v___x_3131_);
                lean_ctor_set_uint8(
                    v___x_3132_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___y_3130_,
                );
                v___x_3133_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(
                    v___x_3132_,
                    v_a_3089_,
                    v_a_3090_,
                    v_a_3091_,
                    v_a_3092_,
                    v_a_3093_,
                    v_a_3094_,
                    v_a_3095_,
                    v_a_3096_,
                    v_a_3097_,
                    v_a_3098_,
                    v_a_3099_,
                );
                if lean_obj_tag(v___x_3133_) == 0 {
                    v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
                    lean_inc(v_a_3134_);
                    lean_dec_ref_known(v___x_3133_, 1);
                    v_p_3135_ = lean_ctor_get(v_a_3134_, 0);
                    lean_inc(v_a_3120_);
                    lean_inc_ref(v_p_3135_);
                    v___x_3136_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(
                        v_p_3135_, v_a_3120_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_,
                        v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_,
                        v_a_3099_,
                    );
                    if lean_obj_tag(v___x_3136_) == 0 {
                        v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
                        lean_inc(v_a_3137_);
                        lean_dec_ref_known(v___x_3136_, 1);
                        v___x_3138_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(
                            v_a_3137_,
                            v___x_3101_,
                            v_a_3120_,
                            v_a_3089_,
                            v_a_3090_,
                            v_a_3091_,
                            v_a_3092_,
                            v_a_3093_,
                            v_a_3094_,
                            v_a_3095_,
                            v_a_3096_,
                            v_a_3097_,
                            v_a_3098_,
                            v_a_3099_,
                        );
                        if lean_obj_tag(v___x_3138_) == 0 {
                            v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
                            v_isSharedCheck_3152_ = (!lean_is_exclusive(v___x_3138_)) as u8;
                            if v_isSharedCheck_3152_ == 0 {
                                v___x_3141_ = v___x_3138_;
                                v_isShared_3142_ = v_isSharedCheck_3152_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_3139_);
                                lean_dec(v___x_3138_);
                                v___x_3141_ = lean_box(0);
                                v_isShared_3142_ = v_isSharedCheck_3152_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3134_);
                            v_a_3153_ = lean_ctor_get(v___x_3138_, 0);
                            v_isSharedCheck_3160_ = (!lean_is_exclusive(v___x_3138_)) as u8;
                            if v_isSharedCheck_3160_ == 0 {
                                v___x_3155_ = v___x_3138_;
                                v_isShared_3156_ = v_isSharedCheck_3160_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_3153_);
                                lean_dec(v___x_3138_);
                                v___x_3155_ = lean_box(0);
                                v_isShared_3156_ = v_isSharedCheck_3160_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3134_);
                        lean_dec(v_a_3120_);
                        v_a_3161_ = lean_ctor_get(v___x_3136_, 0);
                        v_isSharedCheck_3168_ = (!lean_is_exclusive(v___x_3136_)) as u8;
                        if v_isSharedCheck_3168_ == 0 {
                            v___x_3163_ = v___x_3136_;
                            v_isShared_3164_ = v_isSharedCheck_3168_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3161_);
                            lean_dec(v___x_3136_);
                            v___x_3163_ = lean_box(0);
                            v_isShared_3164_ = v_isSharedCheck_3168_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3120_);
                    v_a_3169_ = lean_ctor_get(v___x_3133_, 0);
                    v_isSharedCheck_3176_ = (!lean_is_exclusive(v___x_3133_)) as u8;
                    if v_isSharedCheck_3176_ == 0 {
                        v___x_3171_ = v___x_3133_;
                        v_isShared_3172_ = v_isSharedCheck_3176_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3169_);
                        lean_dec(v___x_3133_);
                        v___x_3171_ = lean_box(0);
                        v_isShared_3172_ = v_isSharedCheck_3176_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                if lean_obj_tag(v_a_3139_) == 1 {
                    lean_del_object(v___x_3141_);
                    v_val_3143_ = lean_ctor_get(v_a_3139_, 0);
                    lean_inc_n(v_val_3143_, 2);
                    lean_dec_ref_known(v_a_3139_, 1);
                    v___x_3144_ = l_Lean_Grind_Linarith_Expr_norm(v_val_3143_);
                    v___x_3145_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3145_, 0, v_a_3134_);
                    lean_ctor_set(v___x_3145_, 1, v_val_3143_);
                    v___x_3146_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v___x_3146_, 0, v___x_3144_);
                    lean_ctor_set(v___x_3146_, 1, v___x_3145_);
                    lean_ctor_set_uint8(
                        v___x_3146_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v___y_3130_,
                    );
                    v___x_3147_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(
                        v___x_3146_,
                        v_a_3089_,
                        v_a_3090_,
                        v_a_3091_,
                        v_a_3092_,
                        v_a_3093_,
                        v_a_3094_,
                        v_a_3095_,
                        v_a_3096_,
                        v_a_3097_,
                        v_a_3098_,
                        v_a_3099_,
                    );
                    return v___x_3147_;
                } else {
                    lean_dec(v_a_3139_);
                    lean_dec(v_a_3134_);
                    v___x_3148_ = lean_box(0);
                    if v_isShared_3142_ == 0 {
                        lean_ctor_set(v___x_3141_, 0, v___x_3148_);
                        v___x_3150_ = v___x_3141_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3148_);
                        v___x_3150_ = v_reuseFailAlloc_3151_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_3150_;
            }
            6 => {
                if v_isShared_3156_ == 0 {
                    v___x_3158_ = v___x_3155_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
                    v___x_3158_ = v_reuseFailAlloc_3159_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3158_;
            }
            8 => {
                if v_isShared_3164_ == 0 {
                    v___x_3166_ = v___x_3163_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
                    v___x_3166_ = v_reuseFailAlloc_3167_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3166_;
            }
            10 => {
                if v_isShared_3172_ == 0 {
                    v___x_3174_ = v___x_3171_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
                    v___x_3174_ = v_reuseFailAlloc_3175_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3174_;
            }
            12 => {
                if v_isShared_3181_ == 0 {
                    v___x_3183_ = v___x_3180_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
                    v___x_3183_ = v_reuseFailAlloc_3184_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3183_;
            }
            14 => {
                if lean_obj_tag(v_a_3197_) == 1 {
                    lean_del_object(v___x_3199_);
                    v_val_3201_ = lean_ctor_get(v_a_3197_, 0);
                    lean_inc_n(v_val_3201_, 2);
                    lean_dec_ref_known(v_a_3197_, 1);
                    v___x_3202_ = l_Lean_Grind_Linarith_Expr_norm(v_val_3201_);
                    v___x_3203_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3203_, 0, v_a_3192_);
                    lean_ctor_set(v___x_3203_, 1, v_val_3201_);
                    v___x_3204_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v___x_3204_, 0, v___x_3202_);
                    lean_ctor_set(v___x_3204_, 1, v___x_3203_);
                    lean_ctor_set_uint8(
                        v___x_3204_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_strict_3087_,
                    );
                    v___x_3205_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(
                        v___x_3204_,
                        v_a_3089_,
                        v_a_3090_,
                        v_a_3091_,
                        v_a_3092_,
                        v_a_3093_,
                        v_a_3094_,
                        v_a_3095_,
                        v_a_3096_,
                        v_a_3097_,
                        v_a_3098_,
                        v_a_3099_,
                    );
                    return v___x_3205_;
                } else {
                    lean_dec(v_a_3197_);
                    lean_dec(v_a_3192_);
                    v___x_3206_ = lean_box(0);
                    if v_isShared_3200_ == 0 {
                        lean_ctor_set(v___x_3199_, 0, v___x_3206_);
                        v___x_3208_ = v___x_3199_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3206_);
                        v___x_3208_ = v_reuseFailAlloc_3209_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                return v___x_3208_;
            }
            16 => {
                if v_isShared_3214_ == 0 {
                    v___x_3216_ = v___x_3213_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
                    v___x_3216_ = v_reuseFailAlloc_3217_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3216_;
            }
            18 => {
                if v_isShared_3222_ == 0 {
                    v___x_3224_ = v___x_3221_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
                    v___x_3224_ = v_reuseFailAlloc_3225_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3224_;
            }
            20 => {
                if v_isShared_3230_ == 0 {
                    v___x_3232_ = v___x_3229_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
                    v___x_3232_ = v_reuseFailAlloc_3233_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3232_;
            }
            22 => {
                if v_isShared_3238_ == 0 {
                    v___x_3240_ = v___x_3237_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
                    v___x_3240_ = v_reuseFailAlloc_3241_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3240_;
            }
            24 => {
                return v___x_3245_;
            }
            25 => {
                if v_isShared_3251_ == 0 {
                    v___x_3253_ = v___x_3250_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
                    v___x_3253_ = v_reuseFailAlloc_3254_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3253_;
            }
            27 => {
                return v___x_3258_;
            }
            28 => {
                if v_isShared_3264_ == 0 {
                    v___x_3266_ = v___x_3263_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
                    v___x_3266_ = v_reuseFailAlloc_3267_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_3269_: *mut LeanObject = *_args.add(0);
    let mut v_lhs_3270_: *mut LeanObject = *_args.add(1);
    let mut v_rhs_3271_: *mut LeanObject = *_args.add(2);
    let mut v_strict_3272_: *mut LeanObject = *_args.add(3);
    let mut v_eqTrue_3273_: *mut LeanObject = *_args.add(4);
    let mut v_a_3274_: *mut LeanObject = *_args.add(5);
    let mut v_a_3275_: *mut LeanObject = *_args.add(6);
    let mut v_a_3276_: *mut LeanObject = *_args.add(7);
    let mut v_a_3277_: *mut LeanObject = *_args.add(8);
    let mut v_a_3278_: *mut LeanObject = *_args.add(9);
    let mut v_a_3279_: *mut LeanObject = *_args.add(10);
    let mut v_a_3280_: *mut LeanObject = *_args.add(11);
    let mut v_a_3281_: *mut LeanObject = *_args.add(12);
    let mut v_a_3282_: *mut LeanObject = *_args.add(13);
    let mut v_a_3283_: *mut LeanObject = *_args.add(14);
    let mut v_a_3284_: *mut LeanObject = *_args.add(15);
    let mut v_a_3285_: *mut LeanObject = *_args.add(16);
    let mut v_strict_boxed_3286_: u8 = 0;
    let mut v_eqTrue_boxed_3287_: u8 = 0;
    let mut v_res_3288_: *mut LeanObject = core::ptr::null_mut();
    v_strict_boxed_3286_ = (lean_unbox(v_strict_3272_) as u8);
    v_eqTrue_boxed_3287_ = (lean_unbox(v_eqTrue_3273_) as u8);
    v_res_3288_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(v_e_3269_, v_lhs_3270_, v_rhs_3271_, v_strict_boxed_3286_, v_eqTrue_boxed_3287_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_);
    lean_dec(v_a_3284_);
    lean_dec_ref(v_a_3283_);
    lean_dec(v_a_3282_);
    lean_dec_ref(v_a_3281_);
    lean_dec(v_a_3280_);
    lean_dec_ref(v_a_3279_);
    lean_dec(v_a_3278_);
    lean_dec_ref(v_a_3277_);
    lean_dec(v_a_3276_);
    lean_dec(v_a_3275_);
    lean_dec(v_a_3274_);
    return v_res_3288_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(
    mut v_e_3289_: *mut LeanObject,
    mut v_lhs_3290_: *mut LeanObject,
    mut v_rhs_3291_: *mut LeanObject,
    mut v_strict_3292_: u8,
    mut v_eqTrue_3293_: u8,
    mut v_a_3294_: *mut LeanObject,
    mut v_a_3295_: *mut LeanObject,
    mut v_a_3296_: *mut LeanObject,
    mut v_a_3297_: *mut LeanObject,
    mut v_a_3298_: *mut LeanObject,
    mut v_a_3299_: *mut LeanObject,
    mut v_a_3300_: *mut LeanObject,
    mut v_a_3301_: *mut LeanObject,
    mut v_a_3302_: *mut LeanObject,
    mut v_a_3303_: *mut LeanObject,
    mut v_a_3304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: u8 = 0;
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v_val_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3321_: u8 = 0;
    let mut v_val_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: u8 = 0;
    let mut v___f_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3332_: u8 = 0;
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: u8 = 0;
    let mut v_a_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3340_: u8 = 0;
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3344_: u8 = 0;
    let mut v_val_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3355_: u8 = 0;
    let mut v_a_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3359_: u8 = 0;
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3363_: u8 = 0;
    let mut v_a_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3367_: u8 = 0;
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3371_: u8 = 0;
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3376_: u8 = 0;
    let mut v_a_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3380_: u8 = 0;
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3384_: u8 = 0;
    let mut v_a_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3388_: u8 = 0;
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3392_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3306_ = l_Lean_Meta_Grind_getGeneration___redArg(v_lhs_3290_, v_a_3295_);
                if lean_obj_tag(v___x_3306_) == 0 {
                    v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
                    lean_inc(v_a_3307_);
                    lean_dec_ref_known(v___x_3306_, 1);
                    v___x_3308_ = 0;
                    v___x_3309_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(
                        v_lhs_3290_,
                        v___x_3308_,
                        v_a_3307_,
                        v_a_3294_,
                        v_a_3295_,
                        v_a_3296_,
                        v_a_3297_,
                        v_a_3298_,
                        v_a_3299_,
                        v_a_3300_,
                        v_a_3301_,
                        v_a_3302_,
                        v_a_3303_,
                        v_a_3304_,
                    );
                    if lean_obj_tag(v___x_3309_) == 0 {
                        v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
                        v_isSharedCheck_3376_ = (!lean_is_exclusive(v___x_3309_)) as u8;
                        if v_isSharedCheck_3376_ == 0 {
                            v___x_3312_ = v___x_3309_;
                            v_isShared_3313_ = v_isSharedCheck_3376_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3310_);
                            lean_dec(v___x_3309_);
                            v___x_3312_ = lean_box(0);
                            v_isShared_3313_ = v_isSharedCheck_3376_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_rhs_3291_);
                        lean_dec_ref(v_e_3289_);
                        v_a_3377_ = lean_ctor_get(v___x_3309_, 0);
                        v_isSharedCheck_3384_ = (!lean_is_exclusive(v___x_3309_)) as u8;
                        if v_isSharedCheck_3384_ == 0 {
                            v___x_3379_ = v___x_3309_;
                            v_isShared_3380_ = v_isSharedCheck_3384_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_3377_);
                            lean_dec(v___x_3309_);
                            v___x_3379_ = lean_box(0);
                            v_isShared_3380_ = v_isSharedCheck_3384_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_rhs_3291_);
                    lean_dec_ref(v_lhs_3290_);
                    lean_dec_ref(v_e_3289_);
                    v_a_3385_ = lean_ctor_get(v___x_3306_, 0);
                    v_isSharedCheck_3392_ = (!lean_is_exclusive(v___x_3306_)) as u8;
                    if v_isSharedCheck_3392_ == 0 {
                        v___x_3387_ = v___x_3306_;
                        v_isShared_3388_ = v_isSharedCheck_3392_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_3385_);
                        lean_dec(v___x_3306_);
                        v___x_3387_ = lean_box(0);
                        v_isShared_3388_ = v_isSharedCheck_3392_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3310_) == 1 {
                    lean_del_object(v___x_3312_);
                    v_val_3314_ = lean_ctor_get(v_a_3310_, 0);
                    lean_inc(v_val_3314_);
                    lean_dec_ref_known(v_a_3310_, 1);
                    v___x_3315_ = l_Lean_Meta_Grind_getGeneration___redArg(v_rhs_3291_, v_a_3295_);
                    if lean_obj_tag(v___x_3315_) == 0 {
                        v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
                        lean_inc(v_a_3316_);
                        lean_dec_ref_known(v___x_3315_, 1);
                        v___x_3317_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(
                            v_rhs_3291_,
                            v___x_3308_,
                            v_a_3316_,
                            v_a_3294_,
                            v_a_3295_,
                            v_a_3296_,
                            v_a_3297_,
                            v_a_3298_,
                            v_a_3299_,
                            v_a_3300_,
                            v_a_3301_,
                            v_a_3302_,
                            v_a_3303_,
                            v_a_3304_,
                        );
                        if lean_obj_tag(v___x_3317_) == 0 {
                            v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
                            v_isSharedCheck_3355_ = (!lean_is_exclusive(v___x_3317_)) as u8;
                            if v_isSharedCheck_3355_ == 0 {
                                v___x_3320_ = v___x_3317_;
                                v_isShared_3321_ = v_isSharedCheck_3355_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_3318_);
                                lean_dec(v___x_3317_);
                                v___x_3320_ = lean_box(0);
                                v_isShared_3321_ = v_isSharedCheck_3355_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_val_3314_);
                            lean_dec_ref(v_e_3289_);
                            v_a_3356_ = lean_ctor_get(v___x_3317_, 0);
                            v_isSharedCheck_3363_ = (!lean_is_exclusive(v___x_3317_)) as u8;
                            if v_isSharedCheck_3363_ == 0 {
                                v___x_3358_ = v___x_3317_;
                                v_isShared_3359_ = v_isSharedCheck_3363_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_3356_);
                                lean_dec(v___x_3317_);
                                v___x_3358_ = lean_box(0);
                                v_isShared_3359_ = v_isSharedCheck_3363_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_3314_);
                        lean_dec_ref(v_rhs_3291_);
                        lean_dec_ref(v_e_3289_);
                        v_a_3364_ = lean_ctor_get(v___x_3315_, 0);
                        v_isSharedCheck_3371_ = (!lean_is_exclusive(v___x_3315_)) as u8;
                        if v_isSharedCheck_3371_ == 0 {
                            v___x_3366_ = v___x_3315_;
                            v_isShared_3367_ = v_isSharedCheck_3371_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_3364_);
                            lean_dec(v___x_3315_);
                            v___x_3366_ = lean_box(0);
                            v_isShared_3367_ = v_isSharedCheck_3371_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3310_);
                    lean_dec_ref(v_rhs_3291_);
                    lean_dec_ref(v_e_3289_);
                    v___x_3372_ = lean_box(0);
                    if v_isShared_3313_ == 0 {
                        lean_ctor_set(v___x_3312_, 0, v___x_3372_);
                        v___x_3374_ = v___x_3312_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3375_, 0, v___x_3372_);
                        v___x_3374_ = v_reuseFailAlloc_3375_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_3318_) == 1 {
                    lean_del_object(v___x_3320_);
                    if v_eqTrue_3293_ == 0 {
                        v_val_3322_ = lean_ctor_get(v_a_3318_, 0);
                        lean_inc(v_val_3322_);
                        lean_dec_ref_known(v_a_3318_, 1);
                        v___x_3323_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(
                            v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_,
                            v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_,
                        );
                        if lean_obj_tag(v___x_3323_) == 0 {
                            v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
                            lean_inc(v_a_3324_);
                            lean_dec_ref_known(v___x_3323_, 1);
                            v___x_3325_ = (lean_unbox(v_a_3324_) as u8);
                            if v___x_3325_ == 0 {
                                lean_dec(v_a_3324_);
                                lean_dec(v_val_3322_);
                                lean_dec(v_val_3314_);
                                lean_inc(v_a_3294_);
                                v___f_3326_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                                lean_closure_set(v___f_3326_, 0, v_a_3294_);
                                lean_closure_set(v___f_3326_, 1, v_e_3289_);
                                v___x_3327_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                                v___x_3328_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3327_, v___f_3326_, v_a_3295_);
                                return v___x_3328_;
                            } else {
                                lean_inc(v_val_3314_);
                                lean_inc(v_val_3322_);
                                v___x_3329_ = lean_alloc_ctor(3, 2, (0) as u32);
                                lean_ctor_set(v___x_3329_, 0, v_val_3322_);
                                lean_ctor_set(v___x_3329_, 1, v_val_3314_);
                                v___x_3330_ = l_Lean_Grind_Linarith_Expr_norm(v___x_3329_);
                                if v_strict_3292_ == 0 {
                                    v___x_3336_ = (lean_unbox(v_a_3324_) as u8);
                                    lean_dec(v_a_3324_);
                                    v___y_3332_ = v___x_3336_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_a_3324_);
                                    v___y_3332_ = v_eqTrue_3293_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_val_3322_);
                            lean_dec(v_val_3314_);
                            lean_dec_ref(v_e_3289_);
                            v_a_3337_ = lean_ctor_get(v___x_3323_, 0);
                            v_isSharedCheck_3344_ = (!lean_is_exclusive(v___x_3323_)) as u8;
                            if v_isSharedCheck_3344_ == 0 {
                                v___x_3339_ = v___x_3323_;
                                v_isShared_3340_ = v_isSharedCheck_3344_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_3337_);
                                lean_dec(v___x_3323_);
                                v___x_3339_ = lean_box(0);
                                v_isShared_3340_ = v_isSharedCheck_3344_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_val_3345_ = lean_ctor_get(v_a_3318_, 0);
                        lean_inc_n(v_val_3345_, 2);
                        lean_dec_ref_known(v_a_3318_, 1);
                        lean_inc(v_val_3314_);
                        v___x_3346_ = lean_alloc_ctor(3, 2, (0) as u32);
                        lean_ctor_set(v___x_3346_, 0, v_val_3314_);
                        lean_ctor_set(v___x_3346_, 1, v_val_3345_);
                        v___x_3347_ = l_Lean_Grind_Linarith_Expr_norm(v___x_3346_);
                        v___x_3348_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_3348_, 0, v_e_3289_);
                        lean_ctor_set(v___x_3348_, 1, v_val_3314_);
                        lean_ctor_set(v___x_3348_, 2, v_val_3345_);
                        v___x_3349_ = lean_alloc_ctor(0, 2, (1) as u32);
                        lean_ctor_set(v___x_3349_, 0, v___x_3347_);
                        lean_ctor_set(v___x_3349_, 1, v___x_3348_);
                        lean_ctor_set_uint8(
                            v___x_3349_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            v_strict_3292_,
                        );
                        v___x_3350_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(
                            v___x_3349_,
                            v_a_3294_,
                            v_a_3295_,
                            v_a_3296_,
                            v_a_3297_,
                            v_a_3298_,
                            v_a_3299_,
                            v_a_3300_,
                            v_a_3301_,
                            v_a_3302_,
                            v_a_3303_,
                            v_a_3304_,
                        );
                        return v___x_3350_;
                    }
                } else {
                    lean_dec(v_a_3318_);
                    lean_dec(v_val_3314_);
                    lean_dec_ref(v_e_3289_);
                    v___x_3351_ = lean_box(0);
                    if v_isShared_3321_ == 0 {
                        lean_ctor_set(v___x_3320_, 0, v___x_3351_);
                        v___x_3353_ = v___x_3320_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3351_);
                        v___x_3353_ = v_reuseFailAlloc_3354_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3333_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3333_, 0, v_e_3289_);
                lean_ctor_set(v___x_3333_, 1, v_val_3314_);
                lean_ctor_set(v___x_3333_, 2, v_val_3322_);
                v___x_3334_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_3334_, 0, v___x_3330_);
                lean_ctor_set(v___x_3334_, 1, v___x_3333_);
                lean_ctor_set_uint8(
                    v___x_3334_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___y_3332_,
                );
                v___x_3335_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(
                    v___x_3334_,
                    v_a_3294_,
                    v_a_3295_,
                    v_a_3296_,
                    v_a_3297_,
                    v_a_3298_,
                    v_a_3299_,
                    v_a_3300_,
                    v_a_3301_,
                    v_a_3302_,
                    v_a_3303_,
                    v_a_3304_,
                );
                return v___x_3335_;
            }
            4 => {
                if v_isShared_3340_ == 0 {
                    v___x_3342_ = v___x_3339_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
                    v___x_3342_ = v_reuseFailAlloc_3343_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3342_;
            }
            6 => {
                return v___x_3353_;
            }
            7 => {
                if v_isShared_3359_ == 0 {
                    v___x_3361_ = v___x_3358_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
                    v___x_3361_ = v_reuseFailAlloc_3362_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3361_;
            }
            9 => {
                if v_isShared_3367_ == 0 {
                    v___x_3369_ = v___x_3366_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
                    v___x_3369_ = v_reuseFailAlloc_3370_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3369_;
            }
            11 => {
                return v___x_3374_;
            }
            12 => {
                if v_isShared_3380_ == 0 {
                    v___x_3382_ = v___x_3379_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
                    v___x_3382_ = v_reuseFailAlloc_3383_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3382_;
            }
            14 => {
                if v_isShared_3388_ == 0 {
                    v___x_3390_ = v___x_3387_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
                    v___x_3390_ = v_reuseFailAlloc_3391_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3390_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_3393_: *mut LeanObject = *_args.add(0);
    let mut v_lhs_3394_: *mut LeanObject = *_args.add(1);
    let mut v_rhs_3395_: *mut LeanObject = *_args.add(2);
    let mut v_strict_3396_: *mut LeanObject = *_args.add(3);
    let mut v_eqTrue_3397_: *mut LeanObject = *_args.add(4);
    let mut v_a_3398_: *mut LeanObject = *_args.add(5);
    let mut v_a_3399_: *mut LeanObject = *_args.add(6);
    let mut v_a_3400_: *mut LeanObject = *_args.add(7);
    let mut v_a_3401_: *mut LeanObject = *_args.add(8);
    let mut v_a_3402_: *mut LeanObject = *_args.add(9);
    let mut v_a_3403_: *mut LeanObject = *_args.add(10);
    let mut v_a_3404_: *mut LeanObject = *_args.add(11);
    let mut v_a_3405_: *mut LeanObject = *_args.add(12);
    let mut v_a_3406_: *mut LeanObject = *_args.add(13);
    let mut v_a_3407_: *mut LeanObject = *_args.add(14);
    let mut v_a_3408_: *mut LeanObject = *_args.add(15);
    let mut v_a_3409_: *mut LeanObject = *_args.add(16);
    let mut v_strict_boxed_3410_: u8 = 0;
    let mut v_eqTrue_boxed_3411_: u8 = 0;
    let mut v_res_3412_: *mut LeanObject = core::ptr::null_mut();
    v_strict_boxed_3410_ = (lean_unbox(v_strict_3396_) as u8);
    v_eqTrue_boxed_3411_ = (lean_unbox(v_eqTrue_3397_) as u8);
    v_res_3412_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(v_e_3393_, v_lhs_3394_, v_rhs_3395_, v_strict_boxed_3410_, v_eqTrue_boxed_3411_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
    lean_dec(v_a_3408_);
    lean_dec_ref(v_a_3407_);
    lean_dec(v_a_3406_);
    lean_dec_ref(v_a_3405_);
    lean_dec(v_a_3404_);
    lean_dec_ref(v_a_3403_);
    lean_dec(v_a_3402_);
    lean_dec_ref(v_a_3401_);
    lean_dec(v_a_3400_);
    lean_dec(v_a_3399_);
    lean_dec(v_a_3398_);
    return v_res_3412_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(
    mut v_e_3413_: *mut LeanObject,
    mut v_lhs_3414_: *mut LeanObject,
    mut v_rhs_3415_: *mut LeanObject,
    mut v_strict_3416_: u8,
    mut v_eqTrue_3417_: u8,
    mut v_a_3418_: *mut LeanObject,
    mut v_a_3419_: *mut LeanObject,
    mut v_a_3420_: *mut LeanObject,
    mut v_a_3421_: *mut LeanObject,
    mut v_a_3422_: *mut LeanObject,
    mut v_a_3423_: *mut LeanObject,
    mut v_a_3424_: *mut LeanObject,
    mut v_a_3425_: *mut LeanObject,
    mut v_a_3426_: *mut LeanObject,
    mut v_a_3427_: *mut LeanObject,
    mut v_a_3428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3440_: u8 = 0;
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_structId_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: u8 = 0;
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3450_: u8 = 0;
    let mut v_val_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3458_: u8 = 0;
    let mut v_val_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3464_: u8 = 0;
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: u8 = 0;
    let mut v_reuseFailAlloc_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3482_: u8 = 0;
    let mut v_a_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3486_: u8 = 0;
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3490_: u8 = 0;
    let mut v_a_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3494_: u8 = 0;
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3498_: u8 = 0;
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3503_: u8 = 0;
    let mut v_a_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3507_: u8 = 0;
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3511_: u8 = 0;
    let mut v_a_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3515_: u8 = 0;
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3519_: u8 = 0;
    let mut v_isSharedCheck_3520_: u8 = 0;
    let mut v_unused_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3525_: u8 = 0;
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3529_: u8 = 0;
    let mut v_a_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3533_: u8 = 0;
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3537_: u8 = 0;
    let mut v_a_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3541_: u8 = 0;
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3430_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
                    v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_,
                    v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_,
                );
                if lean_obj_tag(v___x_3430_) == 0 {
                    v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
                    lean_inc(v_a_3431_);
                    lean_dec_ref_known(v___x_3430_, 1);
                    lean_inc_ref(v_lhs_3414_);
                    v___x_3432_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(
                        v_lhs_3414_,
                        v_a_3418_,
                        v_a_3419_,
                        v_a_3420_,
                        v_a_3421_,
                        v_a_3422_,
                        v_a_3423_,
                        v_a_3424_,
                        v_a_3425_,
                        v_a_3426_,
                        v_a_3427_,
                        v_a_3428_,
                    );
                    if lean_obj_tag(v___x_3432_) == 0 {
                        v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
                        lean_inc(v_a_3433_);
                        lean_dec_ref_known(v___x_3432_, 1);
                        v_fst_3434_ = lean_ctor_get(v_a_3433_, 0);
                        lean_inc(v_fst_3434_);
                        lean_dec(v_a_3433_);
                        lean_inc_ref(v_rhs_3415_);
                        v___x_3435_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(
                            v_rhs_3415_,
                            v_a_3418_,
                            v_a_3419_,
                            v_a_3420_,
                            v_a_3421_,
                            v_a_3422_,
                            v_a_3423_,
                            v_a_3424_,
                            v_a_3425_,
                            v_a_3426_,
                            v_a_3427_,
                            v_a_3428_,
                        );
                        if lean_obj_tag(v___x_3435_) == 0 {
                            v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
                            lean_inc(v_a_3436_);
                            lean_dec_ref_known(v___x_3435_, 1);
                            v_fst_3437_ = lean_ctor_get(v_a_3436_, 0);
                            v_isSharedCheck_3520_ = (!lean_is_exclusive(v_a_3436_)) as u8;
                            if v_isSharedCheck_3520_ == 0 {
                                v_unused_3521_ = lean_ctor_get(v_a_3436_, 1);
                                lean_dec(v_unused_3521_);
                                v___x_3439_ = v_a_3436_;
                                v_isShared_3440_ = v_isSharedCheck_3520_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_fst_3437_);
                                lean_dec(v_a_3436_);
                                v___x_3439_ = lean_box(0);
                                v_isShared_3440_ = v_isSharedCheck_3520_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_fst_3434_);
                            lean_dec(v_a_3431_);
                            lean_dec_ref(v_rhs_3415_);
                            lean_dec_ref(v_lhs_3414_);
                            lean_dec_ref(v_e_3413_);
                            v_a_3522_ = lean_ctor_get(v___x_3435_, 0);
                            v_isSharedCheck_3529_ = (!lean_is_exclusive(v___x_3435_)) as u8;
                            if v_isSharedCheck_3529_ == 0 {
                                v___x_3524_ = v___x_3435_;
                                v_isShared_3525_ = v_isSharedCheck_3529_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc(v_a_3522_);
                                lean_dec(v___x_3435_);
                                v___x_3524_ = lean_box(0);
                                v_isShared_3525_ = v_isSharedCheck_3529_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3431_);
                        lean_dec_ref(v_rhs_3415_);
                        lean_dec_ref(v_lhs_3414_);
                        lean_dec_ref(v_e_3413_);
                        v_a_3530_ = lean_ctor_get(v___x_3432_, 0);
                        v_isSharedCheck_3537_ = (!lean_is_exclusive(v___x_3432_)) as u8;
                        if v_isSharedCheck_3537_ == 0 {
                            v___x_3532_ = v___x_3432_;
                            v_isShared_3533_ = v_isSharedCheck_3537_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_3530_);
                            lean_dec(v___x_3432_);
                            v___x_3532_ = lean_box(0);
                            v_isShared_3533_ = v_isSharedCheck_3537_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_rhs_3415_);
                    lean_dec_ref(v_lhs_3414_);
                    lean_dec_ref(v_e_3413_);
                    v_a_3538_ = lean_ctor_get(v___x_3430_, 0);
                    v_isSharedCheck_3545_ = (!lean_is_exclusive(v___x_3430_)) as u8;
                    if v_isSharedCheck_3545_ == 0 {
                        v___x_3540_ = v___x_3430_;
                        v_isShared_3541_ = v_isSharedCheck_3545_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_3538_);
                        lean_dec(v___x_3430_);
                        v___x_3540_ = lean_box(0);
                        v_isShared_3541_ = v_isSharedCheck_3545_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3441_ = l_Lean_Meta_Grind_getGeneration___redArg(v_lhs_3414_, v_a_3419_);
                lean_dec_ref(v_lhs_3414_);
                if lean_obj_tag(v___x_3441_) == 0 {
                    v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
                    lean_inc(v_a_3442_);
                    lean_dec_ref_known(v___x_3441_, 1);
                    v_id_3443_ = lean_ctor_get(v_a_3431_, 0);
                    lean_inc(v_id_3443_);
                    v_structId_3444_ = lean_ctor_get(v_a_3431_, 1);
                    lean_inc(v_structId_3444_);
                    lean_dec(v_a_3431_);
                    v___x_3445_ = 0;
                    v___x_3446_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(
                        v_fst_3434_,
                        v___x_3445_,
                        v_a_3442_,
                        v_structId_3444_,
                        v_a_3419_,
                        v_a_3420_,
                        v_a_3421_,
                        v_a_3422_,
                        v_a_3423_,
                        v_a_3424_,
                        v_a_3425_,
                        v_a_3426_,
                        v_a_3427_,
                        v_a_3428_,
                    );
                    if lean_obj_tag(v___x_3446_) == 0 {
                        v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
                        v_isSharedCheck_3503_ = (!lean_is_exclusive(v___x_3446_)) as u8;
                        if v_isSharedCheck_3503_ == 0 {
                            v___x_3449_ = v___x_3446_;
                            v_isShared_3450_ = v_isSharedCheck_3503_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3447_);
                            lean_dec(v___x_3446_);
                            v___x_3449_ = lean_box(0);
                            v_isShared_3450_ = v_isSharedCheck_3503_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_structId_3444_);
                        lean_dec(v_id_3443_);
                        lean_del_object(v___x_3439_);
                        lean_dec(v_fst_3437_);
                        lean_dec_ref(v_rhs_3415_);
                        lean_dec_ref(v_e_3413_);
                        v_a_3504_ = lean_ctor_get(v___x_3446_, 0);
                        v_isSharedCheck_3511_ = (!lean_is_exclusive(v___x_3446_)) as u8;
                        if v_isSharedCheck_3511_ == 0 {
                            v___x_3506_ = v___x_3446_;
                            v_isShared_3507_ = v_isSharedCheck_3511_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_3504_);
                            lean_dec(v___x_3446_);
                            v___x_3506_ = lean_box(0);
                            v_isShared_3507_ = v_isSharedCheck_3511_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3439_);
                    lean_dec(v_fst_3437_);
                    lean_dec(v_fst_3434_);
                    lean_dec(v_a_3431_);
                    lean_dec_ref(v_rhs_3415_);
                    lean_dec_ref(v_e_3413_);
                    v_a_3512_ = lean_ctor_get(v___x_3441_, 0);
                    v_isSharedCheck_3519_ = (!lean_is_exclusive(v___x_3441_)) as u8;
                    if v_isSharedCheck_3519_ == 0 {
                        v___x_3514_ = v___x_3441_;
                        v_isShared_3515_ = v_isSharedCheck_3519_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_3512_);
                        lean_dec(v___x_3441_);
                        v___x_3514_ = lean_box(0);
                        v_isShared_3515_ = v_isSharedCheck_3519_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_3447_) == 1 {
                    lean_del_object(v___x_3449_);
                    v_val_3451_ = lean_ctor_get(v_a_3447_, 0);
                    lean_inc(v_val_3451_);
                    lean_dec_ref_known(v_a_3447_, 1);
                    v___x_3452_ = l_Lean_Meta_Grind_getGeneration___redArg(v_rhs_3415_, v_a_3419_);
                    lean_dec_ref(v_rhs_3415_);
                    if lean_obj_tag(v___x_3452_) == 0 {
                        v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
                        lean_inc(v_a_3453_);
                        lean_dec_ref_known(v___x_3452_, 1);
                        v___x_3454_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(
                            v_fst_3437_,
                            v___x_3445_,
                            v_a_3453_,
                            v_structId_3444_,
                            v_a_3419_,
                            v_a_3420_,
                            v_a_3421_,
                            v_a_3422_,
                            v_a_3423_,
                            v_a_3424_,
                            v_a_3425_,
                            v_a_3426_,
                            v_a_3427_,
                            v_a_3428_,
                        );
                        if lean_obj_tag(v___x_3454_) == 0 {
                            v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
                            v_isSharedCheck_3482_ = (!lean_is_exclusive(v___x_3454_)) as u8;
                            if v_isSharedCheck_3482_ == 0 {
                                v___x_3457_ = v___x_3454_;
                                v_isShared_3458_ = v_isSharedCheck_3482_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_3455_);
                                lean_dec(v___x_3454_);
                                v___x_3457_ = lean_box(0);
                                v_isShared_3458_ = v_isSharedCheck_3482_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_val_3451_);
                            lean_dec(v_structId_3444_);
                            lean_dec(v_id_3443_);
                            lean_del_object(v___x_3439_);
                            lean_dec_ref(v_e_3413_);
                            v_a_3483_ = lean_ctor_get(v___x_3454_, 0);
                            v_isSharedCheck_3490_ = (!lean_is_exclusive(v___x_3454_)) as u8;
                            if v_isSharedCheck_3490_ == 0 {
                                v___x_3485_ = v___x_3454_;
                                v_isShared_3486_ = v_isSharedCheck_3490_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_3483_);
                                lean_dec(v___x_3454_);
                                v___x_3485_ = lean_box(0);
                                v_isShared_3486_ = v_isSharedCheck_3490_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_3451_);
                        lean_dec(v_structId_3444_);
                        lean_dec(v_id_3443_);
                        lean_del_object(v___x_3439_);
                        lean_dec(v_fst_3437_);
                        lean_dec_ref(v_e_3413_);
                        v_a_3491_ = lean_ctor_get(v___x_3452_, 0);
                        v_isSharedCheck_3498_ = (!lean_is_exclusive(v___x_3452_)) as u8;
                        if v_isSharedCheck_3498_ == 0 {
                            v___x_3493_ = v___x_3452_;
                            v_isShared_3494_ = v_isSharedCheck_3498_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_3491_);
                            lean_dec(v___x_3452_);
                            v___x_3493_ = lean_box(0);
                            v_isShared_3494_ = v_isSharedCheck_3498_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3447_);
                    lean_dec(v_structId_3444_);
                    lean_dec(v_id_3443_);
                    lean_del_object(v___x_3439_);
                    lean_dec(v_fst_3437_);
                    lean_dec_ref(v_rhs_3415_);
                    lean_dec_ref(v_e_3413_);
                    v___x_3499_ = lean_box(0);
                    if v_isShared_3450_ == 0 {
                        lean_ctor_set(v___x_3449_, 0, v___x_3499_);
                        v___x_3501_ = v___x_3449_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
                        v___x_3501_ = v_reuseFailAlloc_3502_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_a_3455_) == 1 {
                    lean_del_object(v___x_3457_);
                    if v_eqTrue_3417_ == 0 {
                        v_val_3459_ = lean_ctor_get(v_a_3455_, 0);
                        lean_inc_n(v_val_3459_, 2);
                        lean_dec_ref_known(v_a_3455_, 1);
                        lean_inc(v_val_3451_);
                        if v_isShared_3440_ == 0 {
                            lean_ctor_set_tag(v___x_3439_, 3);
                            lean_ctor_set(v___x_3439_, 1, v_val_3451_);
                            lean_ctor_set(v___x_3439_, 0, v_val_3459_);
                            v___x_3461_ = v___x_3439_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3469_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_val_3459_);
                            lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_val_3451_);
                            v___x_3461_ = v_reuseFailAlloc_3469_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_val_3470_ = lean_ctor_get(v_a_3455_, 0);
                        lean_inc_n(v_val_3470_, 2);
                        lean_dec_ref_known(v_a_3455_, 1);
                        lean_inc(v_val_3451_);
                        if v_isShared_3440_ == 0 {
                            lean_ctor_set_tag(v___x_3439_, 3);
                            lean_ctor_set(v___x_3439_, 1, v_val_3470_);
                            lean_ctor_set(v___x_3439_, 0, v_val_3451_);
                            v___x_3472_ = v___x_3439_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3477_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_val_3451_);
                            lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_val_3470_);
                            v___x_3472_ = v_reuseFailAlloc_3477_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3455_);
                    lean_dec(v_val_3451_);
                    lean_dec(v_structId_3444_);
                    lean_dec(v_id_3443_);
                    lean_del_object(v___x_3439_);
                    lean_dec_ref(v_e_3413_);
                    v___x_3478_ = lean_box(0);
                    if v_isShared_3458_ == 0 {
                        lean_ctor_set(v___x_3457_, 0, v___x_3478_);
                        v___x_3480_ = v___x_3457_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3478_);
                        v___x_3480_ = v_reuseFailAlloc_3481_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3462_ = l_Lean_Grind_Linarith_Expr_norm(v___x_3461_);
                if v_strict_3416_ == 0 {
                    v___x_3468_ = 1;
                    v___y_3464_ = v___x_3468_;
                    state = 5;
                    continue;
                } else {
                    v___y_3464_ = v_eqTrue_3417_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3465_ = lean_alloc_ctor(4, 4, (0) as u32);
                lean_ctor_set(v___x_3465_, 0, v_e_3413_);
                lean_ctor_set(v___x_3465_, 1, v_id_3443_);
                lean_ctor_set(v___x_3465_, 2, v_val_3451_);
                lean_ctor_set(v___x_3465_, 3, v_val_3459_);
                v___x_3466_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_3466_, 0, v___x_3462_);
                lean_ctor_set(v___x_3466_, 1, v___x_3465_);
                lean_ctor_set_uint8(
                    v___x_3466_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___y_3464_,
                );
                v___x_3467_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(
                    v___x_3466_,
                    v_structId_3444_,
                    v_a_3419_,
                    v_a_3420_,
                    v_a_3421_,
                    v_a_3422_,
                    v_a_3423_,
                    v_a_3424_,
                    v_a_3425_,
                    v_a_3426_,
                    v_a_3427_,
                    v_a_3428_,
                );
                lean_dec(v_structId_3444_);
                return v___x_3467_;
            }
            6 => {
                v___x_3473_ = l_Lean_Grind_Linarith_Expr_norm(v___x_3472_);
                v___x_3474_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3474_, 0, v_e_3413_);
                lean_ctor_set(v___x_3474_, 1, v_id_3443_);
                lean_ctor_set(v___x_3474_, 2, v_val_3451_);
                lean_ctor_set(v___x_3474_, 3, v_val_3470_);
                v___x_3475_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_3475_, 0, v___x_3473_);
                lean_ctor_set(v___x_3475_, 1, v___x_3474_);
                lean_ctor_set_uint8(
                    v___x_3475_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_strict_3416_,
                );
                v___x_3476_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(
                    v___x_3475_,
                    v_structId_3444_,
                    v_a_3419_,
                    v_a_3420_,
                    v_a_3421_,
                    v_a_3422_,
                    v_a_3423_,
                    v_a_3424_,
                    v_a_3425_,
                    v_a_3426_,
                    v_a_3427_,
                    v_a_3428_,
                );
                lean_dec(v_structId_3444_);
                return v___x_3476_;
            }
            7 => {
                return v___x_3480_;
            }
            8 => {
                if v_isShared_3486_ == 0 {
                    v___x_3488_ = v___x_3485_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
                    v___x_3488_ = v_reuseFailAlloc_3489_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3488_;
            }
            10 => {
                if v_isShared_3494_ == 0 {
                    v___x_3496_ = v___x_3493_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
                    v___x_3496_ = v_reuseFailAlloc_3497_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3496_;
            }
            12 => {
                return v___x_3501_;
            }
            13 => {
                if v_isShared_3507_ == 0 {
                    v___x_3509_ = v___x_3506_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
                    v___x_3509_ = v_reuseFailAlloc_3510_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3509_;
            }
            15 => {
                if v_isShared_3515_ == 0 {
                    v___x_3517_ = v___x_3514_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
                    v___x_3517_ = v_reuseFailAlloc_3518_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3517_;
            }
            17 => {
                if v_isShared_3525_ == 0 {
                    v___x_3527_ = v___x_3524_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
                    v___x_3527_ = v_reuseFailAlloc_3528_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3527_;
            }
            19 => {
                if v_isShared_3533_ == 0 {
                    v___x_3535_ = v___x_3532_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3530_);
                    v___x_3535_ = v_reuseFailAlloc_3536_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3535_;
            }
            21 => {
                if v_isShared_3541_ == 0 {
                    v___x_3543_ = v___x_3540_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
                    v___x_3543_ = v_reuseFailAlloc_3544_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3543_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_3546_: *mut LeanObject = *_args.add(0);
    let mut v_lhs_3547_: *mut LeanObject = *_args.add(1);
    let mut v_rhs_3548_: *mut LeanObject = *_args.add(2);
    let mut v_strict_3549_: *mut LeanObject = *_args.add(3);
    let mut v_eqTrue_3550_: *mut LeanObject = *_args.add(4);
    let mut v_a_3551_: *mut LeanObject = *_args.add(5);
    let mut v_a_3552_: *mut LeanObject = *_args.add(6);
    let mut v_a_3553_: *mut LeanObject = *_args.add(7);
    let mut v_a_3554_: *mut LeanObject = *_args.add(8);
    let mut v_a_3555_: *mut LeanObject = *_args.add(9);
    let mut v_a_3556_: *mut LeanObject = *_args.add(10);
    let mut v_a_3557_: *mut LeanObject = *_args.add(11);
    let mut v_a_3558_: *mut LeanObject = *_args.add(12);
    let mut v_a_3559_: *mut LeanObject = *_args.add(13);
    let mut v_a_3560_: *mut LeanObject = *_args.add(14);
    let mut v_a_3561_: *mut LeanObject = *_args.add(15);
    let mut v_a_3562_: *mut LeanObject = *_args.add(16);
    let mut v_strict_boxed_3563_: u8 = 0;
    let mut v_eqTrue_boxed_3564_: u8 = 0;
    let mut v_res_3565_: *mut LeanObject = core::ptr::null_mut();
    v_strict_boxed_3563_ = (lean_unbox(v_strict_3549_) as u8);
    v_eqTrue_boxed_3564_ = (lean_unbox(v_eqTrue_3550_) as u8);
    v_res_3565_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_3546_, v_lhs_3547_, v_rhs_3548_, v_strict_boxed_3563_, v_eqTrue_boxed_3564_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
    lean_dec(v_a_3561_);
    lean_dec_ref(v_a_3560_);
    lean_dec(v_a_3559_);
    lean_dec_ref(v_a_3558_);
    lean_dec(v_a_3557_);
    lean_dec_ref(v_a_3556_);
    lean_dec(v_a_3555_);
    lean_dec_ref(v_a_3554_);
    lean_dec(v_a_3553_);
    lean_dec(v_a_3552_);
    lean_dec(v_a_3551_);
    return v_res_3565_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(
    mut v_x_3566_: *mut LeanObject,
    mut v_x_3567_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_3566_) == 0 {
        if lean_obj_tag(v_x_3567_) == 0 {
            let mut v___x_3568_: u8 = 0;
            v___x_3568_ = 1;
            return v___x_3568_;
        } else {
            let mut v___x_3569_: u8 = 0;
            v___x_3569_ = 0;
            return v___x_3569_;
        }
    } else {
        if lean_obj_tag(v_x_3567_) == 0 {
            let mut v___x_3570_: u8 = 0;
            v___x_3570_ = 0;
            return v___x_3570_;
        } else {
            let mut v_val_3571_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_3572_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3573_: u8 = 0;
            v_val_3571_ = lean_ctor_get(v_x_3566_, 0);
            v_val_3572_ = lean_ctor_get(v_x_3567_, 0);
            v___x_3573_ = lean_expr_eqv(v_val_3571_, v_val_3572_);
            return v___x_3573_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0___boxed(
    mut v_x_3574_: *mut LeanObject,
    mut v_x_3575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3576_: u8 = 0;
    let mut v_r_3577_: *mut LeanObject = core::ptr::null_mut();
    v_res_3576_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(
        v_x_3574_, v_x_3575_,
    );
    lean_dec(v_x_3575_);
    lean_dec(v_x_3574_);
    v_r_3577_ = lean_box((v_res_3576_) as usize);
    return v_r_3577_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_propagateIneq(
    mut v_e_3578_: *mut LeanObject,
    mut v_eqTrue_3579_: u8,
    mut v_a_3580_: *mut LeanObject,
    mut v_a_3581_: *mut LeanObject,
    mut v_a_3582_: *mut LeanObject,
    mut v_a_3583_: *mut LeanObject,
    mut v_a_3584_: *mut LeanObject,
    mut v_a_3585_: *mut LeanObject,
    mut v_a_3586_: *mut LeanObject,
    mut v_a_3587_: *mut LeanObject,
    mut v_a_3588_: *mut LeanObject,
    mut v_a_3589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3595_: u8 = 0;
    let mut v_linarith_3596_: u8 = 0;
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: u8 = 0;
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3615_: u8 = 0;
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_3627_: u8 = 0;
    let mut v___y_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3647_: u8 = 0;
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3651_: u8 = 0;
    let mut v_val_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3657_: u8 = 0;
    let mut v_leFn_x3f_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltFn_x3f_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: u8 = 0;
    let mut v___x_3661_: u8 = 0;
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: u8 = 0;
    let mut v_isSharedCheck_3667_: u8 = 0;
    let mut v_a_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3671_: u8 = 0;
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3675_: u8 = 0;
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3680_: u8 = 0;
    let mut v_val_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3684_: u8 = 0;
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3689_: u8 = 0;
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leInst_x3f_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltInst_x3f_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lawfulOrderLTInst_x3f_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isPreorderInst_x3f_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_orderedAddInst_x3f_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isLinearInst_x3f_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3707_: u8 = 0;
    let mut v___y_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3714_: u8 = 0;
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3727_: u8 = 0;
    let mut v___y_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3734_: u8 = 0;
    let mut v___y_3736_: u8 = 0;
    let mut v_strict_3737_: u8 = 0;
    let mut v___y_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3754_: u8 = 0;
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: u8 = 0;
    let mut v___x_3758_: u8 = 0;
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3765_: u8 = 0;
    let mut v___y_3767_: u8 = 0;
    let mut v___y_3769_: u8 = 0;
    let mut v___x_3770_: u8 = 0;
    let mut v_isSharedCheck_3771_: u8 = 0;
    let mut v_a_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3775_: u8 = 0;
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3779_: u8 = 0;
    let mut v_isSharedCheck_3780_: u8 = 0;
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3785_: u8 = 0;
    let mut v_a_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3789_: u8 = 0;
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3793_: u8 = 0;
    let mut v_isSharedCheck_3794_: u8 = 0;
    let mut v_a_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3798_: u8 = 0;
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3802_: u8 = 0;
    let mut v_isSharedCheck_3803_: u8 = 0;
    let mut v_a_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3807_: u8 = 0;
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3811_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3591_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3582_);
                if lean_obj_tag(v___x_3591_) == 0 {
                    v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
                    v_isSharedCheck_3803_ = (!lean_is_exclusive(v___x_3591_)) as u8;
                    if v_isSharedCheck_3803_ == 0 {
                        v___x_3594_ = v___x_3591_;
                        v_isShared_3595_ = v_isSharedCheck_3803_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3592_);
                        lean_dec(v___x_3591_);
                        v___x_3594_ = lean_box(0);
                        v_isShared_3595_ = v_isSharedCheck_3803_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_3578_);
                    v_a_3804_ = lean_ctor_get(v___x_3591_, 0);
                    v_isSharedCheck_3811_ = (!lean_is_exclusive(v___x_3591_)) as u8;
                    if v_isSharedCheck_3811_ == 0 {
                        v___x_3806_ = v___x_3591_;
                        v_isShared_3807_ = v_isSharedCheck_3811_;
                        state = 35;
                        continue;
                    } else {
                        lean_inc(v_a_3804_);
                        lean_dec(v___x_3591_);
                        v___x_3806_ = lean_box(0);
                        v_isShared_3807_ = v_isSharedCheck_3811_;
                        state = 35;
                        continue;
                    }
                }
            }
            1 => {
                v_linarith_3596_ = lean_ctor_get_uint8(
                    v_a_3592_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 22) as u32,
                );
                lean_dec(v_a_3592_);
                if v_linarith_3596_ == 0 {
                    lean_dec_ref(v_e_3578_);
                    v___x_3597_ = lean_box(0);
                    if v_isShared_3595_ == 0 {
                        lean_ctor_set(v___x_3594_, 0, v___x_3597_);
                        v___x_3599_ = v___x_3594_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3597_);
                        v___x_3599_ = v_reuseFailAlloc_3600_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3601_ = l_Lean_Expr_getAppNumArgs(v_e_3578_);
                    v___x_3602_ = lean_unsigned_to_nat(4);
                    v___x_3603_ = lean_nat_dec_eq(v___x_3601_, v___x_3602_);
                    if v___x_3603_ == 0 {
                        lean_dec(v___x_3601_);
                        lean_dec_ref(v_e_3578_);
                        v___x_3604_ = lean_box(0);
                        if v_isShared_3595_ == 0 {
                            lean_ctor_set(v___x_3594_, 0, v___x_3604_);
                            v___x_3606_ = v___x_3594_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3604_);
                            v___x_3606_ = v_reuseFailAlloc_3607_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3608_ = lean_unsigned_to_nat(1);
                        v___x_3609_ = lean_nat_sub(v___x_3601_, v___x_3608_);
                        lean_inc(v___x_3609_);
                        v___x_3610_ = l_Lean_Expr_getRevArg_x21(v_e_3578_, v___x_3609_);
                        lean_inc_ref(v___x_3610_);
                        v___x_3611_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(
                            v___x_3610_,
                            v_a_3580_,
                            v_a_3581_,
                            v_a_3582_,
                            v_a_3583_,
                            v_a_3584_,
                            v_a_3585_,
                            v_a_3586_,
                            v_a_3587_,
                            v_a_3588_,
                            v_a_3589_,
                        );
                        if lean_obj_tag(v___x_3611_) == 0 {
                            v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
                            v_isSharedCheck_3794_ = (!lean_is_exclusive(v___x_3611_)) as u8;
                            if v_isSharedCheck_3794_ == 0 {
                                v___x_3614_ = v___x_3611_;
                                v_isShared_3615_ = v_isSharedCheck_3794_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_3612_);
                                lean_dec(v___x_3611_);
                                v___x_3614_ = lean_box(0);
                                v_isShared_3615_ = v_isSharedCheck_3794_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_3610_);
                            lean_dec(v___x_3609_);
                            lean_dec(v___x_3601_);
                            lean_del_object(v___x_3594_);
                            lean_dec_ref(v_e_3578_);
                            v_a_3795_ = lean_ctor_get(v___x_3611_, 0);
                            v_isSharedCheck_3802_ = (!lean_is_exclusive(v___x_3611_)) as u8;
                            if v_isSharedCheck_3802_ == 0 {
                                v___x_3797_ = v___x_3611_;
                                v_isShared_3798_ = v_isSharedCheck_3802_;
                                state = 33;
                                continue;
                            } else {
                                lean_inc(v_a_3795_);
                                lean_dec(v___x_3611_);
                                v___x_3797_ = lean_box(0);
                                v_isShared_3798_ = v_isSharedCheck_3802_;
                                state = 33;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_3599_;
            }
            3 => {
                return v___x_3606_;
            }
            4 => {
                v___x_3616_ = lean_nat_sub(v___x_3609_, v___x_3608_);
                lean_dec(v___x_3609_);
                v___x_3617_ = l_Lean_Expr_getRevArg_x21(v_e_3578_, v___x_3616_);
                v___x_3618_ = lean_unsigned_to_nat(2);
                v___x_3619_ = lean_nat_sub(v___x_3601_, v___x_3618_);
                v___x_3620_ = lean_nat_sub(v___x_3619_, v___x_3608_);
                lean_dec(v___x_3619_);
                v___x_3621_ = l_Lean_Expr_getRevArg_x21(v_e_3578_, v___x_3620_);
                v___x_3622_ = lean_unsigned_to_nat(3);
                v___x_3623_ = lean_nat_sub(v___x_3601_, v___x_3622_);
                lean_dec(v___x_3601_);
                v___x_3624_ = lean_nat_sub(v___x_3623_, v___x_3608_);
                lean_dec(v___x_3623_);
                v___x_3625_ = l_Lean_Expr_getRevArg_x21(v_e_3578_, v___x_3624_);
                if lean_obj_tag(v_a_3612_) == 1 {
                    lean_del_object(v___x_3614_);
                    lean_dec_ref(v___x_3610_);
                    lean_del_object(v___x_3594_);
                    v_val_3652_ = lean_ctor_get(v_a_3612_, 0);
                    lean_inc(v_val_3652_);
                    lean_dec_ref_known(v_a_3612_, 1);
                    v___x_3653_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                        v_val_3652_,
                        v_a_3580_,
                        v_a_3581_,
                        v_a_3582_,
                        v_a_3583_,
                        v_a_3584_,
                        v_a_3585_,
                        v_a_3586_,
                        v_a_3587_,
                        v_a_3588_,
                        v_a_3589_,
                    );
                    if lean_obj_tag(v___x_3653_) == 0 {
                        v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
                        v_isSharedCheck_3667_ = (!lean_is_exclusive(v___x_3653_)) as u8;
                        if v_isSharedCheck_3667_ == 0 {
                            v___x_3656_ = v___x_3653_;
                            v_isShared_3657_ = v_isSharedCheck_3667_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3654_);
                            lean_dec(v___x_3653_);
                            v___x_3656_ = lean_box(0);
                            v_isShared_3657_ = v_isSharedCheck_3667_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_3652_);
                        lean_dec_ref(v___x_3625_);
                        lean_dec_ref(v___x_3621_);
                        lean_dec_ref(v___x_3617_);
                        lean_dec_ref(v_e_3578_);
                        v_a_3668_ = lean_ctor_get(v___x_3653_, 0);
                        v_isSharedCheck_3675_ = (!lean_is_exclusive(v___x_3653_)) as u8;
                        if v_isSharedCheck_3675_ == 0 {
                            v___x_3670_ = v___x_3653_;
                            v_isShared_3671_ = v_isSharedCheck_3675_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_3668_);
                            lean_dec(v___x_3653_);
                            v___x_3670_ = lean_box(0);
                            v_isShared_3671_ = v_isSharedCheck_3675_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3612_);
                    v___x_3676_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(
                        v___x_3610_,
                        v_a_3580_,
                        v_a_3581_,
                        v_a_3582_,
                        v_a_3583_,
                        v_a_3584_,
                        v_a_3585_,
                        v_a_3586_,
                        v_a_3587_,
                        v_a_3588_,
                        v_a_3589_,
                    );
                    if lean_obj_tag(v___x_3676_) == 0 {
                        v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
                        v_isSharedCheck_3785_ = (!lean_is_exclusive(v___x_3676_)) as u8;
                        if v_isSharedCheck_3785_ == 0 {
                            v___x_3679_ = v___x_3676_;
                            v_isShared_3680_ = v_isSharedCheck_3785_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_3677_);
                            lean_dec(v___x_3676_);
                            v___x_3679_ = lean_box(0);
                            v_isShared_3680_ = v_isSharedCheck_3785_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_3625_);
                        lean_dec_ref(v___x_3621_);
                        lean_dec_ref(v___x_3617_);
                        lean_del_object(v___x_3614_);
                        lean_del_object(v___x_3594_);
                        lean_dec_ref(v_e_3578_);
                        v_a_3786_ = lean_ctor_get(v___x_3676_, 0);
                        v_isSharedCheck_3793_ = (!lean_is_exclusive(v___x_3676_)) as u8;
                        if v_isSharedCheck_3793_ == 0 {
                            v___x_3788_ = v___x_3676_;
                            v_isShared_3789_ = v_isSharedCheck_3793_;
                            state = 31;
                            continue;
                        } else {
                            lean_inc(v_a_3786_);
                            lean_dec(v___x_3676_);
                            v___x_3788_ = lean_box(0);
                            v_isShared_3789_ = v_isSharedCheck_3793_;
                            state = 31;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_3639_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(
                    v___y_3628_,
                    v___y_3629_,
                    v___y_3630_,
                    v___y_3631_,
                    v___y_3632_,
                    v___y_3633_,
                    v___y_3634_,
                    v___y_3635_,
                    v___y_3636_,
                    v___y_3637_,
                    v___y_3638_,
                );
                if lean_obj_tag(v___x_3639_) == 0 {
                    v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
                    lean_inc(v_a_3640_);
                    lean_dec_ref_known(v___x_3639_, 1);
                    v___x_3641_ = (lean_unbox(v_a_3640_) as u8);
                    lean_dec(v_a_3640_);
                    if v___x_3641_ == 0 {
                        v___x_3642_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(v_e_3578_, v___x_3621_, v___x_3625_, v_strict_3627_, v_eqTrue_3579_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
                        lean_dec(v___y_3628_);
                        return v___x_3642_;
                    } else {
                        v___x_3643_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(v_e_3578_, v___x_3621_, v___x_3625_, v_strict_3627_, v_eqTrue_3579_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
                        lean_dec(v___y_3628_);
                        return v___x_3643_;
                    }
                } else {
                    lean_dec(v___y_3628_);
                    lean_dec_ref(v___x_3625_);
                    lean_dec_ref(v___x_3621_);
                    lean_dec_ref(v_e_3578_);
                    v_a_3644_ = lean_ctor_get(v___x_3639_, 0);
                    v_isSharedCheck_3651_ = (!lean_is_exclusive(v___x_3639_)) as u8;
                    if v_isSharedCheck_3651_ == 0 {
                        v___x_3646_ = v___x_3639_;
                        v_isShared_3647_ = v_isSharedCheck_3651_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3644_);
                        lean_dec(v___x_3639_);
                        v___x_3646_ = lean_box(0);
                        v_isShared_3647_ = v_isSharedCheck_3651_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3647_ == 0 {
                    v___x_3649_ = v___x_3646_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
                    v___x_3649_ = v_reuseFailAlloc_3650_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3649_;
            }
            8 => {
                v_leFn_x3f_3658_ = lean_ctor_get(v_a_3654_, 20);
                lean_inc(v_leFn_x3f_3658_);
                v_ltFn_x3f_3659_ = lean_ctor_get(v_a_3654_, 21);
                lean_inc(v_ltFn_x3f_3659_);
                lean_dec(v_a_3654_);
                v___x_3660_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_leFn_x3f_3658_, v___x_3617_);
                lean_dec(v_leFn_x3f_3658_);
                if v___x_3660_ == 0 {
                    v___x_3661_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_ltFn_x3f_3659_, v___x_3617_);
                    lean_dec_ref(v___x_3617_);
                    lean_dec(v_ltFn_x3f_3659_);
                    if v___x_3661_ == 0 {
                        lean_dec(v_val_3652_);
                        lean_dec_ref(v___x_3625_);
                        lean_dec_ref(v___x_3621_);
                        lean_dec_ref(v_e_3578_);
                        v___x_3662_ = lean_box(0);
                        if v_isShared_3657_ == 0 {
                            lean_ctor_set(v___x_3656_, 0, v___x_3662_);
                            v___x_3664_ = v___x_3656_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3662_);
                            v___x_3664_ = v_reuseFailAlloc_3665_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3656_);
                        v_strict_3627_ = v___x_3603_;
                        v___y_3628_ = v_val_3652_;
                        v___y_3629_ = v_a_3580_;
                        v___y_3630_ = v_a_3581_;
                        v___y_3631_ = v_a_3582_;
                        v___y_3632_ = v_a_3583_;
                        v___y_3633_ = v_a_3584_;
                        v___y_3634_ = v_a_3585_;
                        v___y_3635_ = v_a_3586_;
                        v___y_3636_ = v_a_3587_;
                        v___y_3637_ = v_a_3588_;
                        v___y_3638_ = v_a_3589_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_ltFn_x3f_3659_);
                    lean_del_object(v___x_3656_);
                    lean_dec_ref(v___x_3617_);
                    v___x_3666_ = 0;
                    v_strict_3627_ = v___x_3666_;
                    v___y_3628_ = v_val_3652_;
                    v___y_3629_ = v_a_3580_;
                    v___y_3630_ = v_a_3581_;
                    v___y_3631_ = v_a_3582_;
                    v___y_3632_ = v_a_3583_;
                    v___y_3633_ = v_a_3584_;
                    v___y_3634_ = v_a_3585_;
                    v___y_3635_ = v_a_3586_;
                    v___y_3636_ = v_a_3587_;
                    v___y_3637_ = v_a_3588_;
                    v___y_3638_ = v_a_3589_;
                    state = 5;
                    continue;
                }
            }
            9 => {
                return v___x_3664_;
            }
            10 => {
                if v_isShared_3671_ == 0 {
                    v___x_3673_ = v___x_3670_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3668_);
                    v___x_3673_ = v_reuseFailAlloc_3674_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3673_;
            }
            12 => {
                if lean_obj_tag(v_a_3677_) == 1 {
                    v_val_3681_ = lean_ctor_get(v_a_3677_, 0);
                    v_isSharedCheck_3780_ = (!lean_is_exclusive(v_a_3677_)) as u8;
                    if v_isSharedCheck_3780_ == 0 {
                        v___x_3683_ = v_a_3677_;
                        v_isShared_3684_ = v_isSharedCheck_3780_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_val_3681_);
                        lean_dec(v_a_3677_);
                        v___x_3683_ = lean_box(0);
                        v_isShared_3684_ = v_isSharedCheck_3780_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3677_);
                    lean_dec_ref(v___x_3625_);
                    lean_dec_ref(v___x_3621_);
                    lean_dec_ref(v___x_3617_);
                    lean_del_object(v___x_3614_);
                    lean_del_object(v___x_3594_);
                    lean_dec_ref(v_e_3578_);
                    v___x_3781_ = lean_box(0);
                    if v_isShared_3680_ == 0 {
                        lean_ctor_set(v___x_3679_, 0, v___x_3781_);
                        v___x_3783_ = v___x_3679_;
                        state = 30;
                        continue;
                    } else {
                        v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3781_);
                        v___x_3783_ = v_reuseFailAlloc_3784_;
                        state = 30;
                        continue;
                    }
                }
            }
            13 => {
                v___x_3685_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
                    v_val_3681_,
                    v_a_3580_,
                    v_a_3581_,
                    v_a_3582_,
                    v_a_3583_,
                    v_a_3584_,
                    v_a_3585_,
                    v_a_3586_,
                    v_a_3587_,
                    v_a_3588_,
                    v_a_3589_,
                );
                if lean_obj_tag(v___x_3685_) == 0 {
                    v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
                    v_isSharedCheck_3771_ = (!lean_is_exclusive(v___x_3685_)) as u8;
                    if v_isSharedCheck_3771_ == 0 {
                        v___x_3688_ = v___x_3685_;
                        v_isShared_3689_ = v_isSharedCheck_3771_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_3686_);
                        lean_dec(v___x_3685_);
                        v___x_3688_ = lean_box(0);
                        v_isShared_3689_ = v_isSharedCheck_3771_;
                        state = 14;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3683_);
                    lean_dec(v_val_3681_);
                    lean_del_object(v___x_3679_);
                    lean_dec_ref(v___x_3625_);
                    lean_dec_ref(v___x_3621_);
                    lean_dec_ref(v___x_3617_);
                    lean_del_object(v___x_3614_);
                    lean_del_object(v___x_3594_);
                    lean_dec_ref(v_e_3578_);
                    v_a_3772_ = lean_ctor_get(v___x_3685_, 0);
                    v_isSharedCheck_3779_ = (!lean_is_exclusive(v___x_3685_)) as u8;
                    if v_isSharedCheck_3779_ == 0 {
                        v___x_3774_ = v___x_3685_;
                        v_isShared_3775_ = v_isSharedCheck_3779_;
                        state = 28;
                        continue;
                    } else {
                        lean_inc(v_a_3772_);
                        lean_dec(v___x_3685_);
                        v___x_3774_ = lean_box(0);
                        v_isShared_3775_ = v_isSharedCheck_3779_;
                        state = 28;
                        continue;
                    }
                }
            }
            14 => {
                v_leInst_x3f_3695_ = lean_ctor_get(v_a_3686_, 5);
                lean_inc(v_leInst_x3f_3695_);
                v_ltInst_x3f_3696_ = lean_ctor_get(v_a_3686_, 6);
                lean_inc(v_ltInst_x3f_3696_);
                v_lawfulOrderLTInst_x3f_3697_ = lean_ctor_get(v_a_3686_, 7);
                lean_inc(v_lawfulOrderLTInst_x3f_3697_);
                v_isPreorderInst_x3f_3698_ = lean_ctor_get(v_a_3686_, 8);
                lean_inc(v_isPreorderInst_x3f_3698_);
                v_orderedAddInst_x3f_3699_ = lean_ctor_get(v_a_3686_, 9);
                lean_inc(v_orderedAddInst_x3f_3699_);
                v_isLinearInst_x3f_3700_ = lean_ctor_get(v_a_3686_, 10);
                lean_inc(v_isLinearInst_x3f_3700_);
                lean_dec(v_a_3686_);
                if lean_obj_tag(v_leInst_x3f_3695_) == 0 {
                    if v___x_3603_ == 0 {
                        v___y_3769_ = v___x_3603_;
                        state = 27;
                        continue;
                    } else {
                        lean_dec(v_isPreorderInst_x3f_3698_);
                        v___y_3767_ = v___x_3603_;
                        state = 26;
                        continue;
                    }
                } else {
                    v___x_3770_ = 0;
                    v___y_3769_ = v___x_3770_;
                    state = 27;
                    continue;
                }
            }
            15 => {
                v___x_3691_ = lean_box(0);
                if v_isShared_3689_ == 0 {
                    lean_ctor_set(v___x_3688_, 0, v___x_3691_);
                    v___x_3693_ = v___x_3688_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3691_);
                    v___x_3693_ = v_reuseFailAlloc_3694_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3693_;
            }
            17 => {
                if v___y_3714_ == 0 {
                    lean_dec(v_isLinearInst_x3f_3700_);
                    lean_del_object(v___x_3679_);
                    v___x_3715_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_3578_, v___x_3621_, v___x_3625_, v___y_3707_, v_eqTrue_3579_, v___y_3708_, v___y_3702_, v___y_3704_, v___y_3710_, v___y_3703_, v___y_3705_, v___y_3711_, v___y_3712_, v___y_3706_, v___y_3713_, v___y_3709_);
                    lean_dec(v___y_3708_);
                    return v___x_3715_;
                } else {
                    if lean_obj_tag(v_isLinearInst_x3f_3700_) == 0 {
                        lean_dec(v___y_3708_);
                        lean_dec_ref(v___x_3625_);
                        lean_dec_ref(v___x_3621_);
                        lean_dec_ref(v_e_3578_);
                        v___x_3716_ = lean_box(0);
                        if v_isShared_3680_ == 0 {
                            lean_ctor_set(v___x_3679_, 0, v___x_3716_);
                            v___x_3718_ = v___x_3679_;
                            state = 18;
                            continue;
                        } else {
                            v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3716_);
                            v___x_3718_ = v_reuseFailAlloc_3719_;
                            state = 18;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_isLinearInst_x3f_3700_, 1);
                        lean_del_object(v___x_3679_);
                        v___x_3720_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_3578_, v___x_3621_, v___x_3625_, v___y_3707_, v_eqTrue_3579_, v___y_3708_, v___y_3702_, v___y_3704_, v___y_3710_, v___y_3703_, v___y_3705_, v___y_3711_, v___y_3712_, v___y_3706_, v___y_3713_, v___y_3709_);
                        lean_dec(v___y_3708_);
                        return v___x_3720_;
                    }
                }
            }
            18 => {
                return v___x_3718_;
            }
            19 => {
                if v_eqTrue_3579_ == 0 {
                    v___y_3702_ = v___y_3722_;
                    v___y_3703_ = v___y_3723_;
                    v___y_3704_ = v___y_3724_;
                    v___y_3705_ = v___y_3725_;
                    v___y_3706_ = v___y_3726_;
                    v___y_3707_ = v___y_3727_;
                    v___y_3708_ = v___y_3728_;
                    v___y_3709_ = v___y_3729_;
                    v___y_3710_ = v___y_3730_;
                    v___y_3711_ = v___y_3731_;
                    v___y_3712_ = v___y_3732_;
                    v___y_3713_ = v___y_3733_;
                    v___y_3714_ = v___x_3603_;
                    state = 17;
                    continue;
                } else {
                    v___y_3702_ = v___y_3722_;
                    v___y_3703_ = v___y_3723_;
                    v___y_3704_ = v___y_3724_;
                    v___y_3705_ = v___y_3725_;
                    v___y_3706_ = v___y_3726_;
                    v___y_3707_ = v___y_3727_;
                    v___y_3708_ = v___y_3728_;
                    v___y_3709_ = v___y_3729_;
                    v___y_3710_ = v___y_3730_;
                    v___y_3711_ = v___y_3731_;
                    v___y_3712_ = v___y_3732_;
                    v___y_3713_ = v___y_3733_;
                    v___y_3714_ = v___y_3734_;
                    state = 17;
                    continue;
                }
            }
            20 => {
                if v_strict_3737_ == 0 {
                    lean_dec(v_lawfulOrderLTInst_x3f_3697_);
                    lean_del_object(v___x_3614_);
                    v___y_3722_ = v___y_3739_;
                    v___y_3723_ = v___y_3742_;
                    v___y_3724_ = v___y_3740_;
                    v___y_3725_ = v___y_3743_;
                    v___y_3726_ = v___y_3746_;
                    v___y_3727_ = v_strict_3737_;
                    v___y_3728_ = v___y_3738_;
                    v___y_3729_ = v___y_3748_;
                    v___y_3730_ = v___y_3741_;
                    v___y_3731_ = v___y_3744_;
                    v___y_3732_ = v___y_3745_;
                    v___y_3733_ = v___y_3747_;
                    v___y_3734_ = v_strict_3737_;
                    state = 19;
                    continue;
                } else {
                    if lean_obj_tag(v_lawfulOrderLTInst_x3f_3697_) == 0 {
                        lean_dec(v___y_3738_);
                        lean_dec(v_isLinearInst_x3f_3700_);
                        lean_del_object(v___x_3679_);
                        lean_dec_ref(v___x_3625_);
                        lean_dec_ref(v___x_3621_);
                        lean_dec_ref(v_e_3578_);
                        v___x_3749_ = lean_box(0);
                        if v_isShared_3615_ == 0 {
                            lean_ctor_set(v___x_3614_, 0, v___x_3749_);
                            v___x_3751_ = v___x_3614_;
                            state = 21;
                            continue;
                        } else {
                            v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3749_);
                            v___x_3751_ = v_reuseFailAlloc_3752_;
                            state = 21;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_lawfulOrderLTInst_x3f_3697_, 1);
                        lean_del_object(v___x_3614_);
                        v___y_3722_ = v___y_3739_;
                        v___y_3723_ = v___y_3742_;
                        v___y_3724_ = v___y_3740_;
                        v___y_3725_ = v___y_3743_;
                        v___y_3726_ = v___y_3746_;
                        v___y_3727_ = v_strict_3737_;
                        v___y_3728_ = v___y_3738_;
                        v___y_3729_ = v___y_3748_;
                        v___y_3730_ = v___y_3741_;
                        v___y_3731_ = v___y_3744_;
                        v___y_3732_ = v___y_3745_;
                        v___y_3733_ = v___y_3747_;
                        v___y_3734_ = v___y_3736_;
                        state = 19;
                        continue;
                    }
                }
            }
            21 => {
                return v___x_3751_;
            }
            22 => {
                if v_isShared_3684_ == 0 {
                    lean_ctor_set(v___x_3683_, 0, v___x_3617_);
                    v___x_3756_ = v___x_3683_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3617_);
                    v___x_3756_ = v_reuseFailAlloc_3763_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_3757_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_3756_, v_leInst_x3f_3695_);
                lean_dec(v_leInst_x3f_3695_);
                if v___x_3757_ == 0 {
                    v___x_3758_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_3756_, v_ltInst_x3f_3696_);
                    lean_dec(v_ltInst_x3f_3696_);
                    lean_dec_ref(v___x_3756_);
                    if v___x_3758_ == 0 {
                        lean_dec(v_isLinearInst_x3f_3700_);
                        lean_dec(v_lawfulOrderLTInst_x3f_3697_);
                        lean_dec(v_val_3681_);
                        lean_del_object(v___x_3679_);
                        lean_dec_ref(v___x_3625_);
                        lean_dec_ref(v___x_3621_);
                        lean_del_object(v___x_3614_);
                        lean_dec_ref(v_e_3578_);
                        v___x_3759_ = lean_box(0);
                        if v_isShared_3595_ == 0 {
                            lean_ctor_set(v___x_3594_, 0, v___x_3759_);
                            v___x_3761_ = v___x_3594_;
                            state = 24;
                            continue;
                        } else {
                            v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3759_);
                            v___x_3761_ = v_reuseFailAlloc_3762_;
                            state = 24;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3594_);
                        v___y_3736_ = v___y_3754_;
                        v_strict_3737_ = v___x_3603_;
                        v___y_3738_ = v_val_3681_;
                        v___y_3739_ = v_a_3580_;
                        v___y_3740_ = v_a_3581_;
                        v___y_3741_ = v_a_3582_;
                        v___y_3742_ = v_a_3583_;
                        v___y_3743_ = v_a_3584_;
                        v___y_3744_ = v_a_3585_;
                        v___y_3745_ = v_a_3586_;
                        v___y_3746_ = v_a_3587_;
                        v___y_3747_ = v_a_3588_;
                        v___y_3748_ = v_a_3589_;
                        state = 20;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_3756_);
                    lean_dec(v_ltInst_x3f_3696_);
                    lean_del_object(v___x_3594_);
                    v___y_3736_ = v___y_3754_;
                    v_strict_3737_ = v___y_3754_;
                    v___y_3738_ = v_val_3681_;
                    v___y_3739_ = v_a_3580_;
                    v___y_3740_ = v_a_3581_;
                    v___y_3741_ = v_a_3582_;
                    v___y_3742_ = v_a_3583_;
                    v___y_3743_ = v_a_3584_;
                    v___y_3744_ = v_a_3585_;
                    v___y_3745_ = v_a_3586_;
                    v___y_3746_ = v_a_3587_;
                    v___y_3747_ = v_a_3588_;
                    v___y_3748_ = v_a_3589_;
                    state = 20;
                    continue;
                }
            }
            24 => {
                return v___x_3761_;
            }
            25 => {
                if lean_obj_tag(v_orderedAddInst_x3f_3699_) == 0 {
                    if v___x_3603_ == 0 {
                        lean_del_object(v___x_3688_);
                        v___y_3754_ = v___x_3603_;
                        state = 22;
                        continue;
                    } else {
                        lean_dec(v_isLinearInst_x3f_3700_);
                        lean_dec(v_lawfulOrderLTInst_x3f_3697_);
                        lean_dec(v_ltInst_x3f_3696_);
                        lean_dec(v_leInst_x3f_3695_);
                        lean_del_object(v___x_3683_);
                        lean_dec(v_val_3681_);
                        lean_del_object(v___x_3679_);
                        lean_dec_ref(v___x_3625_);
                        lean_dec_ref(v___x_3621_);
                        lean_dec_ref(v___x_3617_);
                        lean_del_object(v___x_3614_);
                        lean_del_object(v___x_3594_);
                        lean_dec_ref(v_e_3578_);
                        state = 15;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_orderedAddInst_x3f_3699_, 1);
                    lean_del_object(v___x_3688_);
                    v___y_3754_ = v___y_3765_;
                    state = 22;
                    continue;
                }
            }
            26 => {
                if v___y_3767_ == 0 {
                    v___y_3765_ = v___y_3767_;
                    state = 25;
                    continue;
                } else {
                    lean_dec(v_isLinearInst_x3f_3700_);
                    lean_dec(v_orderedAddInst_x3f_3699_);
                    lean_dec(v_lawfulOrderLTInst_x3f_3697_);
                    lean_dec(v_ltInst_x3f_3696_);
                    lean_dec(v_leInst_x3f_3695_);
                    lean_del_object(v___x_3683_);
                    lean_dec(v_val_3681_);
                    lean_del_object(v___x_3679_);
                    lean_dec_ref(v___x_3625_);
                    lean_dec_ref(v___x_3621_);
                    lean_dec_ref(v___x_3617_);
                    lean_del_object(v___x_3614_);
                    lean_del_object(v___x_3594_);
                    lean_dec_ref(v_e_3578_);
                    state = 15;
                    continue;
                }
            }
            27 => {
                if lean_obj_tag(v_isPreorderInst_x3f_3698_) == 0 {
                    v___y_3767_ = v___x_3603_;
                    state = 26;
                    continue;
                } else {
                    lean_dec_ref_known(v_isPreorderInst_x3f_3698_, 1);
                    v___y_3765_ = v___y_3769_;
                    state = 25;
                    continue;
                }
            }
            28 => {
                if v_isShared_3775_ == 0 {
                    v___x_3777_ = v___x_3774_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3772_);
                    v___x_3777_ = v_reuseFailAlloc_3778_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3777_;
            }
            30 => {
                return v___x_3783_;
            }
            31 => {
                if v_isShared_3789_ == 0 {
                    v___x_3791_ = v___x_3788_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
                    v___x_3791_ = v_reuseFailAlloc_3792_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_3791_;
            }
            33 => {
                if v_isShared_3798_ == 0 {
                    v___x_3800_ = v___x_3797_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_a_3795_);
                    v___x_3800_ = v_reuseFailAlloc_3801_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_3800_;
            }
            35 => {
                if v_isShared_3807_ == 0 {
                    v___x_3809_ = v___x_3806_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3804_);
                    v___x_3809_ = v_reuseFailAlloc_3810_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_3809_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_propagateIneq___boxed(
    mut v_e_3812_: *mut LeanObject,
    mut v_eqTrue_3813_: *mut LeanObject,
    mut v_a_3814_: *mut LeanObject,
    mut v_a_3815_: *mut LeanObject,
    mut v_a_3816_: *mut LeanObject,
    mut v_a_3817_: *mut LeanObject,
    mut v_a_3818_: *mut LeanObject,
    mut v_a_3819_: *mut LeanObject,
    mut v_a_3820_: *mut LeanObject,
    mut v_a_3821_: *mut LeanObject,
    mut v_a_3822_: *mut LeanObject,
    mut v_a_3823_: *mut LeanObject,
    mut v_a_3824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eqTrue_boxed_3825_: u8 = 0;
    let mut v_res_3826_: *mut LeanObject = core::ptr::null_mut();
    v_eqTrue_boxed_3825_ = (lean_unbox(v_eqTrue_3813_) as u8);
    v_res_3826_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(
        v_e_3812_,
        v_eqTrue_boxed_3825_,
        v_a_3814_,
        v_a_3815_,
        v_a_3816_,
        v_a_3817_,
        v_a_3818_,
        v_a_3819_,
        v_a_3820_,
        v_a_3821_,
        v_a_3822_,
        v_a_3823_,
    );
    lean_dec(v_a_3823_);
    lean_dec_ref(v_a_3822_);
    lean_dec(v_a_3821_);
    lean_dec_ref(v_a_3820_);
    lean_dec(v_a_3819_);
    lean_dec_ref(v_a_3818_);
    lean_dec(v_a_3817_);
    lean_dec_ref(v_a_3816_);
    lean_dec(v_a_3815_);
    lean_dec(v_a_3814_);
    return v_res_3826_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
}
