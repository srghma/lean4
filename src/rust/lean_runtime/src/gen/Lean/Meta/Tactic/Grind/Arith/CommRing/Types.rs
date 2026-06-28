// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Types
// Imports: Init.Grind.Ring.CommSemiringAdapter Lean.Meta.Tactic.Grind.Types Lean.Meta.Sym.Arith.Poly
use crate::r#gen::Init::Grind::Ring::CommSemiringAdapter::{
    initialize_Init_Grind_Ring_CommSemiringAdapter,
    runtime_initialize_Init_Grind_Ring_CommSemiringAdapter,
};
use crate::r#gen::Init::Grind::Ring::CommSolver::{
    l_Lean_Grind_CommRing_instInhabitedExpr_default,
    l_Lean_Grind_CommRing_instInhabitedPoly_default,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::l_Lean_Expr_const___override;
use crate::r#gen::Lean::Meta::Sym::Arith::Poly::{
    initialize_Lean_Meta_Sym_Arith_Poly, l_Lean_Grind_CommRing_Poly_degree,
    runtime_initialize_Lean_Meta_Sym_Arith_Poly,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types,
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_SolverExtension_getState___redArg,
    l_Lean_Meta_Grind_registerSolverExtension___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_5, lean_apply_6, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_uint8, lean_ctor_set_usize,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
    lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__0_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__0_value
        ) as *mut LeanObject,
        17542774118954891045 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__1_value
)
    as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommSemiring_default___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommSemiring_default___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommSemiring_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommSemiring: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorIdx(
    mut v_x_391_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_391_) {
        0 => {
            let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
            v___x_392_ = lean_unsigned_to_nat(0);
            return v___x_392_;
        }
        1 => {
            let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
            v___x_393_ = lean_unsigned_to_nat(1);
            return v___x_393_;
        }
        2 => {
            let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
            v___x_394_ = lean_unsigned_to_nat(2);
            return v___x_394_;
        }
        3 => {
            let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
            v___x_395_ = lean_unsigned_to_nat(3);
            return v___x_395_;
        }
        4 => {
            let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
            v___x_396_ = lean_unsigned_to_nat(4);
            return v___x_396_;
        }
        5 => {
            let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
            v___x_397_ = lean_unsigned_to_nat(5);
            return v___x_397_;
        }
        6 => {
            let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
            v___x_398_ = lean_unsigned_to_nat(6);
            return v___x_398_;
        }
        _ => {
            let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
            v___x_399_ = lean_unsigned_to_nat(7);
            return v___x_399_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorIdx___boxed(
    mut v_x_400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_401_: *mut LeanObject = core::ptr::null_mut();
    v_res_401_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorIdx(v_x_400_);
    lean_dec_ref(v_x_400_);
    return v_res_401_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(
    mut v_t_402_: *mut LeanObject,
    mut v_k_403_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_402_) {
        0 => {
            let mut v_a_404_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_405_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ra_406_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rb_407_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
            v_a_404_ = lean_ctor_get(v_t_402_, 0);
            lean_inc_ref(v_a_404_);
            v_b_405_ = lean_ctor_get(v_t_402_, 1);
            lean_inc_ref(v_b_405_);
            v_ra_406_ = lean_ctor_get(v_t_402_, 2);
            lean_inc_ref(v_ra_406_);
            v_rb_407_ = lean_ctor_get(v_t_402_, 3);
            lean_inc_ref(v_rb_407_);
            lean_dec_ref_known(v_t_402_, 4);
            v___x_408_ = lean_apply_4(v_k_403_, v_a_404_, v_b_405_, v_ra_406_, v_rb_407_);
            return v___x_408_;
        }
        1 => {
            let mut v_a_409_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_410_: *mut LeanObject = core::ptr::null_mut();
            let mut v_sa_411_: *mut LeanObject = core::ptr::null_mut();
            let mut v_sb_412_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ra_413_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rb_414_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
            v_a_409_ = lean_ctor_get(v_t_402_, 0);
            lean_inc_ref(v_a_409_);
            v_b_410_ = lean_ctor_get(v_t_402_, 1);
            lean_inc_ref(v_b_410_);
            v_sa_411_ = lean_ctor_get(v_t_402_, 2);
            lean_inc_ref(v_sa_411_);
            v_sb_412_ = lean_ctor_get(v_t_402_, 3);
            lean_inc_ref(v_sb_412_);
            v_ra_413_ = lean_ctor_get(v_t_402_, 4);
            lean_inc_ref(v_ra_413_);
            v_rb_414_ = lean_ctor_get(v_t_402_, 5);
            lean_inc_ref(v_rb_414_);
            lean_dec_ref_known(v_t_402_, 6);
            v___x_415_ = lean_apply_6(
                v_k_403_, v_a_409_, v_b_410_, v_sa_411_, v_sb_412_, v_ra_413_, v_rb_414_,
            );
            return v___x_415_;
        }
        2 => {
            let mut v_k_u2081_416_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_u2081_417_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_418_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_u2082_419_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_u2082_420_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_421_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
            v_k_u2081_416_ = lean_ctor_get(v_t_402_, 0);
            lean_inc(v_k_u2081_416_);
            v_m_u2081_417_ = lean_ctor_get(v_t_402_, 1);
            lean_inc(v_m_u2081_417_);
            v_c_u2081_418_ = lean_ctor_get(v_t_402_, 2);
            lean_inc_ref(v_c_u2081_418_);
            v_k_u2082_419_ = lean_ctor_get(v_t_402_, 3);
            lean_inc(v_k_u2082_419_);
            v_m_u2082_420_ = lean_ctor_get(v_t_402_, 4);
            lean_inc(v_m_u2082_420_);
            v_c_u2082_421_ = lean_ctor_get(v_t_402_, 5);
            lean_inc_ref(v_c_u2082_421_);
            lean_dec_ref_known(v_t_402_, 6);
            v___x_422_ = lean_apply_6(
                v_k_403_,
                v_k_u2081_416_,
                v_m_u2081_417_,
                v_c_u2081_418_,
                v_k_u2082_419_,
                v_m_u2082_420_,
                v_c_u2082_421_,
            );
            return v___x_422_;
        }
        3 => {
            let mut v_k_u2081_423_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_424_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_u2082_425_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_u2082_426_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_427_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
            v_k_u2081_423_ = lean_ctor_get(v_t_402_, 0);
            lean_inc(v_k_u2081_423_);
            v_c_u2081_424_ = lean_ctor_get(v_t_402_, 1);
            lean_inc_ref(v_c_u2081_424_);
            v_k_u2082_425_ = lean_ctor_get(v_t_402_, 2);
            lean_inc(v_k_u2082_425_);
            v_m_u2082_426_ = lean_ctor_get(v_t_402_, 3);
            lean_inc(v_m_u2082_426_);
            v_c_u2082_427_ = lean_ctor_get(v_t_402_, 4);
            lean_inc_ref(v_c_u2082_427_);
            lean_dec_ref_known(v_t_402_, 5);
            v___x_428_ = lean_apply_5(
                v_k_403_,
                v_k_u2081_423_,
                v_c_u2081_424_,
                v_k_u2082_425_,
                v_m_u2082_426_,
                v_c_u2082_427_,
            );
            return v___x_428_;
        }
        6 => {
            let mut v_a_429_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_430_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_431_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_432_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
            v_a_429_ = lean_ctor_get(v_t_402_, 0);
            lean_inc(v_a_429_);
            v_b_430_ = lean_ctor_get(v_t_402_, 1);
            lean_inc(v_b_430_);
            v_c_u2081_431_ = lean_ctor_get(v_t_402_, 2);
            lean_inc_ref(v_c_u2081_431_);
            v_c_u2082_432_ = lean_ctor_get(v_t_402_, 3);
            lean_inc_ref(v_c_u2082_432_);
            lean_dec_ref_known(v_t_402_, 4);
            v___x_433_ = lean_apply_4(v_k_403_, v_a_429_, v_b_430_, v_c_u2081_431_, v_c_u2082_432_);
            return v___x_433_;
        }
        7 => {
            let mut v_k_434_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_435_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_436_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
            v_k_434_ = lean_ctor_get(v_t_402_, 0);
            lean_inc(v_k_434_);
            v_c_u2081_435_ = lean_ctor_get(v_t_402_, 1);
            lean_inc_ref(v_c_u2081_435_);
            v_c_u2082_436_ = lean_ctor_get(v_t_402_, 2);
            lean_inc_ref(v_c_u2082_436_);
            lean_dec_ref_known(v_t_402_, 3);
            v___x_437_ = lean_apply_3(v_k_403_, v_k_434_, v_c_u2081_435_, v_c_u2082_436_);
            return v___x_437_;
        }
        _ => {
            let mut v_k_438_: *mut LeanObject = core::ptr::null_mut();
            let mut v_e_439_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
            v_k_438_ = lean_ctor_get(v_t_402_, 0);
            lean_inc(v_k_438_);
            v_e_439_ = lean_ctor_get(v_t_402_, 1);
            lean_inc_ref(v_e_439_);
            lean_dec_ref(v_t_402_);
            v___x_440_ = lean_apply_2(v_k_403_, v_k_438_, v_e_439_);
            return v___x_440_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim(
    mut v_motive__2_441_: *mut LeanObject,
    mut v_ctorIdx_442_: *mut LeanObject,
    mut v_t_443_: *mut LeanObject,
    mut v_h_444_: *mut LeanObject,
    mut v_k_445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    v___x_446_ =
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_443_, v_k_445_);
    return v___x_446_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___boxed(
    mut v_motive__2_447_: *mut LeanObject,
    mut v_ctorIdx_448_: *mut LeanObject,
    mut v_t_449_: *mut LeanObject,
    mut v_h_450_: *mut LeanObject,
    mut v_k_451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_452_: *mut LeanObject = core::ptr::null_mut();
    v_res_452_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim(
        v_motive__2_447_,
        v_ctorIdx_448_,
        v_t_449_,
        v_h_450_,
        v_k_451_,
    );
    lean_dec(v_ctorIdx_448_);
    return v_res_452_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_core_elim___redArg(
    mut v_t_453_: *mut LeanObject,
    mut v_core_454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    v___x_455_ =
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_453_, v_core_454_);
    return v___x_455_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_core_elim(
    mut v_motive__2_456_: *mut LeanObject,
    mut v_t_457_: *mut LeanObject,
    mut v_h_458_: *mut LeanObject,
    mut v_core_459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    v___x_460_ =
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_457_, v_core_459_);
    return v___x_460_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_coreS_elim___redArg(
    mut v_t_461_: *mut LeanObject,
    mut v_coreS_462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    v___x_463_ =
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_461_, v_coreS_462_);
    return v___x_463_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_coreS_elim(
    mut v_motive__2_464_: *mut LeanObject,
    mut v_t_465_: *mut LeanObject,
    mut v_h_466_: *mut LeanObject,
    mut v_coreS_467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
    v___x_468_ =
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_465_, v_coreS_467_);
    return v___x_468_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_superpose_elim___redArg(
    mut v_t_469_: *mut LeanObject,
    mut v_superpose_470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    v___x_471_ =
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_469_, v_superpose_470_);
    return v___x_471_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_superpose_elim(
    mut v_motive__2_472_: *mut LeanObject,
    mut v_t_473_: *mut LeanObject,
    mut v_h_474_: *mut LeanObject,
    mut v_superpose_475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    v___x_476_ =
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_473_, v_superpose_475_);
    return v___x_476_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_simp_elim___redArg(
    mut v_t_477_: *mut LeanObject,
    mut v_simp_478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    v___x_479_ =
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_477_, v_simp_478_);
    return v___x_479_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_simp_elim(
    mut v_motive__2_480_: *mut LeanObject,
    mut v_t_481_: *mut LeanObject,
    mut v_h_482_: *mut LeanObject,
    mut v_simp_483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    v___x_484_ =
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_481_, v_simp_483_);
    return v___x_484_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_mul_elim___redArg(
    mut v_t_485_: *mut LeanObject,
    mut v_mul_486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    v___x_487_ =
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_485_, v_mul_486_);
    return v___x_487_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_mul_elim(
    mut v_motive__2_488_: *mut LeanObject,
    mut v_t_489_: *mut LeanObject,
    mut v_h_490_: *mut LeanObject,
    mut v_mul_491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    v___x_492_ =
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_489_, v_mul_491_);
    return v___x_492_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_div_elim___redArg(
    mut v_t_493_: *mut LeanObject,
    mut v_div_494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    v___x_495_ =
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_493_, v_div_494_);
    return v___x_495_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_div_elim(
    mut v_motive__2_496_: *mut LeanObject,
    mut v_t_497_: *mut LeanObject,
    mut v_h_498_: *mut LeanObject,
    mut v_div_499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    v___x_500_ =
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_497_, v_div_499_);
    return v___x_500_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_gcd_elim___redArg(
    mut v_t_501_: *mut LeanObject,
    mut v_gcd_502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    v___x_503_ =
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_501_, v_gcd_502_);
    return v___x_503_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_gcd_elim(
    mut v_motive__2_504_: *mut LeanObject,
    mut v_t_505_: *mut LeanObject,
    mut v_h_506_: *mut LeanObject,
    mut v_gcd_507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    v___x_508_ =
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_505_, v_gcd_507_);
    return v___x_508_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_numEq0_elim___redArg(
    mut v_t_509_: *mut LeanObject,
    mut v_numEq0_510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    v___x_511_ =
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_509_, v_numEq0_510_);
    return v___x_511_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_numEq0_elim(
    mut v_motive__2_512_: *mut LeanObject,
    mut v_t_513_: *mut LeanObject,
    mut v_h_514_: *mut LeanObject,
    mut v_numEq0_515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    v___x_516_ =
        l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_513_, v_numEq0_515_);
    return v___x_516_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2()
-> *mut LeanObject {
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    v___x_520_ = lean_box(0);
    v___x_521_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__1;
    v___x_522_ = l_Lean_Expr_const___override(v___x_521_, v___x_520_);
    return v___x_522_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3()
-> *mut LeanObject {
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    v___x_523_ = l_Lean_Grind_CommRing_instInhabitedExpr_default;
    v___x_524_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2,
    );
    v___x_525_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_525_, 0, v___x_524_);
    lean_ctor_set(v___x_525_, 1, v___x_524_);
    lean_ctor_set(v___x_525_, 2, v___x_523_);
    lean_ctor_set(v___x_525_, 3, v___x_523_);
    return v___x_525_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof() -> *mut LeanObject
{
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    v___x_526_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3,
    );
    return v___x_526_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr___closed__0()
-> *mut LeanObject {
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    v___x_527_ = lean_unsigned_to_nat(0);
    v___x_528_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3,
    );
    v___x_529_ = l_Lean_Grind_CommRing_instInhabitedPoly_default;
    v___x_530_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_530_, 0, v___x_529_);
    lean_ctor_set(v___x_530_, 1, v___x_528_);
    lean_ctor_set(v___x_530_, 2, v___x_527_);
    lean_ctor_set(v___x_530_, 3, v___x_527_);
    return v___x_530_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr() -> *mut LeanObject {
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    v___x_531_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr___closed__0,
    );
    return v___x_531_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(
    mut v_c_u2081_532_: *mut LeanObject,
    mut v_c_u2082_533_: *mut LeanObject,
) -> u8 {
    let mut v_p_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sugar_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sugar_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: u8 = 0;
    v_p_534_ = lean_ctor_get(v_c_u2081_532_, 0);
    v_sugar_535_ = lean_ctor_get(v_c_u2081_532_, 2);
    v_id_536_ = lean_ctor_get(v_c_u2081_532_, 3);
    v_p_537_ = lean_ctor_get(v_c_u2082_533_, 0);
    v_sugar_538_ = lean_ctor_get(v_c_u2082_533_, 2);
    v_id_539_ = lean_ctor_get(v_c_u2082_533_, 3);
    v___x_540_ = lean_nat_dec_lt(v_sugar_535_, v_sugar_538_);
    if v___x_540_ == 0 {
        let mut v___x_541_: u8 = 0;
        v___x_541_ = lean_nat_dec_eq(v_sugar_535_, v_sugar_538_);
        if v___x_541_ == 0 {
            let mut v___x_542_: u8 = 0;
            v___x_542_ = 2;
            return v___x_542_;
        } else {
            let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_545_: u8 = 0;
            v___x_543_ = l_Lean_Grind_CommRing_Poly_degree(v_p_534_);
            v___x_544_ = l_Lean_Grind_CommRing_Poly_degree(v_p_537_);
            v___x_545_ = lean_nat_dec_lt(v___x_543_, v___x_544_);
            if v___x_545_ == 0 {
                let mut v___x_546_: u8 = 0;
                v___x_546_ = lean_nat_dec_eq(v___x_543_, v___x_544_);
                lean_dec(v___x_544_);
                lean_dec(v___x_543_);
                if v___x_546_ == 0 {
                    let mut v___x_547_: u8 = 0;
                    v___x_547_ = 2;
                    return v___x_547_;
                } else {
                    let mut v___x_548_: u8 = 0;
                    v___x_548_ = lean_nat_dec_lt(v_id_536_, v_id_539_);
                    if v___x_548_ == 0 {
                        let mut v___x_549_: u8 = 0;
                        v___x_549_ = lean_nat_dec_eq(v_id_536_, v_id_539_);
                        if v___x_549_ == 0 {
                            let mut v___x_550_: u8 = 0;
                            v___x_550_ = 2;
                            return v___x_550_;
                        } else {
                            let mut v___x_551_: u8 = 0;
                            v___x_551_ = 1;
                            return v___x_551_;
                        }
                    } else {
                        let mut v___x_552_: u8 = 0;
                        v___x_552_ = 0;
                        return v___x_552_;
                    }
                }
            } else {
                let mut v___x_553_: u8 = 0;
                lean_dec(v___x_544_);
                lean_dec(v___x_543_);
                v___x_553_ = 0;
                return v___x_553_;
            }
        }
    } else {
        let mut v___x_554_: u8 = 0;
        v___x_554_ = 0;
        return v___x_554_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare___boxed(
    mut v_c_u2081_555_: *mut LeanObject,
    mut v_c_u2082_556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_557_: u8 = 0;
    let mut v_r_558_: *mut LeanObject = core::ptr::null_mut();
    v_res_557_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_c_u2081_555_, v_c_u2082_556_);
    lean_dec_ref(v_c_u2082_556_);
    lean_dec_ref(v_c_u2081_555_);
    v_r_558_ = lean_box((v_res_557_) as usize);
    return v_r_558_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorIdx(
    mut v_x_559_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_559_) {
        0 => {
            let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
            v___x_560_ = lean_unsigned_to_nat(0);
            return v___x_560_;
        }
        1 => {
            let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
            v___x_561_ = lean_unsigned_to_nat(1);
            return v___x_561_;
        }
        _ => {
            let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
            v___x_562_ = lean_unsigned_to_nat(2);
            return v___x_562_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorIdx___boxed(
    mut v_x_563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_564_: *mut LeanObject = core::ptr::null_mut();
    v_res_564_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorIdx(v_x_563_);
    lean_dec_ref(v_x_563_);
    return v_res_564_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(
    mut v_t_565_: *mut LeanObject,
    mut v_k_566_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_565_) {
        0 => {
            let mut v_p_567_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
            v_p_567_ = lean_ctor_get(v_t_565_, 0);
            lean_inc_ref(v_p_567_);
            lean_dec_ref_known(v_t_565_, 1);
            v___x_568_ = lean_apply_1(v_k_566_, v_p_567_);
            return v___x_568_;
        }
        1 => {
            let mut v_p_569_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_u2081_570_: *mut LeanObject = core::ptr::null_mut();
            let mut v_d_571_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_u2082_572_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_u2082_573_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_574_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
            v_p_569_ = lean_ctor_get(v_t_565_, 0);
            lean_inc_ref(v_p_569_);
            v_k_u2081_570_ = lean_ctor_get(v_t_565_, 1);
            lean_inc(v_k_u2081_570_);
            v_d_571_ = lean_ctor_get(v_t_565_, 2);
            lean_inc_ref(v_d_571_);
            v_k_u2082_572_ = lean_ctor_get(v_t_565_, 3);
            lean_inc(v_k_u2082_572_);
            v_m_u2082_573_ = lean_ctor_get(v_t_565_, 4);
            lean_inc(v_m_u2082_573_);
            v_c_574_ = lean_ctor_get(v_t_565_, 5);
            lean_inc_ref(v_c_574_);
            lean_dec_ref_known(v_t_565_, 6);
            v___x_575_ = lean_apply_6(
                v_k_566_,
                v_p_569_,
                v_k_u2081_570_,
                v_d_571_,
                v_k_u2082_572_,
                v_m_u2082_573_,
                v_c_574_,
            );
            return v___x_575_;
        }
        _ => {
            let mut v_p_576_: *mut LeanObject = core::ptr::null_mut();
            let mut v_d_577_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_578_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
            v_p_576_ = lean_ctor_get(v_t_565_, 0);
            lean_inc_ref(v_p_576_);
            v_d_577_ = lean_ctor_get(v_t_565_, 1);
            lean_inc_ref(v_d_577_);
            v_c_578_ = lean_ctor_get(v_t_565_, 2);
            lean_inc_ref(v_c_578_);
            lean_dec_ref_known(v_t_565_, 3);
            v___x_579_ = lean_apply_3(v_k_566_, v_p_576_, v_d_577_, v_c_578_);
            return v___x_579_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim(
    mut v_motive_580_: *mut LeanObject,
    mut v_ctorIdx_581_: *mut LeanObject,
    mut v_t_582_: *mut LeanObject,
    mut v_h_583_: *mut LeanObject,
    mut v_k_584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    v___x_585_ =
        l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_582_, v_k_584_);
    return v___x_585_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___boxed(
    mut v_motive_586_: *mut LeanObject,
    mut v_ctorIdx_587_: *mut LeanObject,
    mut v_t_588_: *mut LeanObject,
    mut v_h_589_: *mut LeanObject,
    mut v_k_590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_591_: *mut LeanObject = core::ptr::null_mut();
    v_res_591_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim(
        v_motive_586_,
        v_ctorIdx_587_,
        v_t_588_,
        v_h_589_,
        v_k_590_,
    );
    lean_dec(v_ctorIdx_587_);
    return v_res_591_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_input_elim___redArg(
    mut v_t_592_: *mut LeanObject,
    mut v_input_593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    v___x_594_ =
        l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_592_, v_input_593_);
    return v___x_594_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_input_elim(
    mut v_motive_595_: *mut LeanObject,
    mut v_t_596_: *mut LeanObject,
    mut v_h_597_: *mut LeanObject,
    mut v_input_598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    v___x_599_ =
        l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_596_, v_input_598_);
    return v___x_599_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_step_elim___redArg(
    mut v_t_600_: *mut LeanObject,
    mut v_step_601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    v___x_602_ =
        l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_600_, v_step_601_);
    return v___x_602_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_step_elim(
    mut v_motive_603_: *mut LeanObject,
    mut v_t_604_: *mut LeanObject,
    mut v_h_605_: *mut LeanObject,
    mut v_step_606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    v___x_607_ =
        l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_604_, v_step_606_);
    return v___x_607_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_normEq0_elim___redArg(
    mut v_t_608_: *mut LeanObject,
    mut v_normEq0_609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    v___x_610_ =
        l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_608_, v_normEq0_609_);
    return v___x_610_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_normEq0_elim(
    mut v_motive_611_: *mut LeanObject,
    mut v_t_612_: *mut LeanObject,
    mut v_h_613_: *mut LeanObject,
    mut v_normEq0_614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    v___x_615_ =
        l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_612_, v_normEq0_614_);
    return v___x_615_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(
    mut v_x_616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_617_: *mut LeanObject = core::ptr::null_mut();
    v_p_617_ = lean_ctor_get(v_x_616_, 0);
    lean_inc_ref(v_p_617_);
    return v_p_617_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p___boxed(
    mut v_x_618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_619_: *mut LeanObject = core::ptr::null_mut();
    v_res_619_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(v_x_618_);
    lean_dec_ref(v_x_618_);
    return v_res_619_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__0()
-> *mut LeanObject {
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    v___x_620_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_620_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__1()
-> *mut LeanObject {
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    v___x_621_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__0,
    );
    v___x_622_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_622_, 0, v___x_621_);
    return v___x_622_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__2()
-> *mut LeanObject {
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    v___x_623_ = lean_unsigned_to_nat(32);
    v___x_624_ = lean_mk_empty_array_with_capacity(v___x_623_);
    v___x_625_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_625_, 0, v___x_624_);
    return v___x_625_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__3()
-> *mut LeanObject {
    let mut v___x_626_: usize = 0;
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    v___x_626_ = 5usize;
    v___x_627_ = lean_unsigned_to_nat(0);
    v___x_628_ = lean_unsigned_to_nat(32);
    v___x_629_ = lean_mk_empty_array_with_capacity(v___x_628_);
    v___x_630_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__2,
    );
    v___x_631_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_631_, 0, v___x_630_);
    lean_ctor_set(v___x_631_, 1, v___x_629_);
    lean_ctor_set(v___x_631_, 2, v___x_627_);
    lean_ctor_set(v___x_631_, 3, v___x_627_);
    lean_ctor_set_usize(v___x_631_, 4, v___x_626_);
    return v___x_631_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__4()
-> *mut LeanObject {
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    v___x_632_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__3,
    );
    v___x_633_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__1,
    );
    v___x_634_ = lean_box(0);
    v___x_635_ = lean_box(0);
    v___x_636_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2,
    );
    v___x_637_ = lean_unsigned_to_nat(0);
    v___x_638_ = lean_alloc_ctor(0, 11, (0) as u32);
    lean_ctor_set(v___x_638_, 0, v___x_637_);
    lean_ctor_set(v___x_638_, 1, v___x_636_);
    lean_ctor_set(v___x_638_, 2, v___x_635_);
    lean_ctor_set(v___x_638_, 3, v___x_636_);
    lean_ctor_set(v___x_638_, 4, v___x_634_);
    lean_ctor_set(v___x_638_, 5, v___x_634_);
    lean_ctor_set(v___x_638_, 6, v___x_634_);
    lean_ctor_set(v___x_638_, 7, v___x_634_);
    lean_ctor_set(v___x_638_, 8, v___x_633_);
    lean_ctor_set(v___x_638_, 9, v___x_632_);
    lean_ctor_set(v___x_638_, 10, v___x_633_);
    return v___x_638_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default()
-> *mut LeanObject {
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    v___x_639_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__4_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__4,
    );
    return v___x_639_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring() -> *mut LeanObject {
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    v___x_640_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default;
    return v___x_640_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default___closed__0()
-> *mut LeanObject {
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    v___x_641_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_641_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default___closed__1()
-> *mut LeanObject {
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    v___x_642_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default___closed__0,
    );
    v___x_643_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_643_, 0, v___x_642_);
    return v___x_643_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default___closed__2()
-> *mut LeanObject {
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    v___x_644_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default___closed__1,
    );
    v___x_645_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default___closed__3,
    );
    v___x_646_ = lean_box(0);
    v___x_647_ = lean_box(0);
    v___x_648_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2,
    );
    v___x_649_ = lean_unsigned_to_nat(0);
    v___x_650_ = lean_alloc_ctor(0, 17, (0) as u32);
    lean_ctor_set(v___x_650_, 0, v___x_649_);
    lean_ctor_set(v___x_650_, 1, v___x_648_);
    lean_ctor_set(v___x_650_, 2, v___x_647_);
    lean_ctor_set(v___x_650_, 3, v___x_648_);
    lean_ctor_set(v___x_650_, 4, v___x_648_);
    lean_ctor_set(v___x_650_, 5, v___x_646_);
    lean_ctor_set(v___x_650_, 6, v___x_646_);
    lean_ctor_set(v___x_650_, 7, v___x_646_);
    lean_ctor_set(v___x_650_, 8, v___x_646_);
    lean_ctor_set(v___x_650_, 9, v___x_646_);
    lean_ctor_set(v___x_650_, 10, v___x_646_);
    lean_ctor_set(v___x_650_, 11, v___x_646_);
    lean_ctor_set(v___x_650_, 12, v___x_646_);
    lean_ctor_set(v___x_650_, 13, v___x_646_);
    lean_ctor_set(v___x_650_, 14, v___x_645_);
    lean_ctor_set(v___x_650_, 15, v___x_644_);
    lean_ctor_set(v___x_650_, 16, v___x_644_);
    return v___x_650_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default() -> *mut LeanObject
{
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    v___x_651_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default___closed__2,
    );
    return v___x_651_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing() -> *mut LeanObject {
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    v___x_652_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default;
    return v___x_652_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    v___x_653_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_653_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    v___x_654_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default_spec__0___closed__0);
    v___x_655_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_655_, 0, v___x_654_);
    return v___x_655_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default_spec__0(
    mut v_00_u03b2_656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    v___x_657_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default_spec__0___closed__1);
    return v___x_657_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__0()
-> *mut LeanObject {
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    v___x_658_ = lean_unsigned_to_nat(32);
    v___x_659_ = lean_mk_empty_array_with_capacity(v___x_658_);
    v___x_660_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_660_, 0, v___x_659_);
    return v___x_660_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__1()
-> *mut LeanObject {
    let mut v___x_661_: usize = 0;
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    v___x_661_ = 5usize;
    v___x_662_ = lean_unsigned_to_nat(0);
    v___x_663_ = lean_unsigned_to_nat(32);
    v___x_664_ = lean_mk_empty_array_with_capacity(v___x_663_);
    v___x_665_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__0,
    );
    v___x_666_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_666_, 0, v___x_665_);
    lean_ctor_set(v___x_666_, 1, v___x_664_);
    lean_ctor_set(v___x_666_, 2, v___x_662_);
    lean_ctor_set(v___x_666_, 3, v___x_662_);
    lean_ctor_set_usize(v___x_666_, 4, v___x_661_);
    return v___x_666_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__2()
-> *mut LeanObject {
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    v___x_667_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default_spec__0(lean_box(0));
    return v___x_667_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__3()
-> *mut LeanObject {
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: u8 = 0;
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    v___x_668_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__2,
    );
    v___x_669_ = 0;
    v___x_670_ = lean_box(0);
    v___x_671_ = lean_box(1);
    v___x_672_ = lean_unsigned_to_nat(0);
    v___x_673_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__1,
    );
    v___x_674_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2,
    );
    v___x_675_ = lean_box(0);
    v___x_676_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default;
    v___x_677_ = lean_alloc_ctor(0, 17, (2) as u32);
    lean_ctor_set(v___x_677_, 0, v___x_676_);
    lean_ctor_set(v___x_677_, 1, v___x_675_);
    lean_ctor_set(v___x_677_, 2, v___x_675_);
    lean_ctor_set(v___x_677_, 3, v___x_674_);
    lean_ctor_set(v___x_677_, 4, v___x_674_);
    lean_ctor_set(v___x_677_, 5, v___x_675_);
    lean_ctor_set(v___x_677_, 6, v___x_675_);
    lean_ctor_set(v___x_677_, 7, v___x_675_);
    lean_ctor_set(v___x_677_, 8, v___x_673_);
    lean_ctor_set(v___x_677_, 9, v___x_672_);
    lean_ctor_set(v___x_677_, 10, v___x_672_);
    lean_ctor_set(v___x_677_, 11, v___x_671_);
    lean_ctor_set(v___x_677_, 12, v___x_670_);
    lean_ctor_set(v___x_677_, 13, v___x_673_);
    lean_ctor_set(v___x_677_, 14, v___x_668_);
    lean_ctor_set(v___x_677_, 15, v___x_672_);
    lean_ctor_set(v___x_677_, 16, v___x_675_);
    lean_ctor_set_uint8(
        v___x_677_,
        (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
        v___x_669_,
    );
    lean_ctor_set_uint8(
        v___x_677_,
        (core::mem::size_of::<*mut LeanObject>() * 17 + 1) as u32,
        v___x_669_,
    );
    return v___x_677_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default()
-> *mut LeanObject {
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    v___x_678_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default___closed__3,
    );
    return v___x_678_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing() -> *mut LeanObject {
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    v___x_679_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default;
    return v___x_679_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommSemiring_default___closed__0()
-> *mut LeanObject {
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    v___x_680_ = lean_box(0);
    v___x_681_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2,
    );
    v___x_682_ = lean_unsigned_to_nat(0);
    v___x_683_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default;
    v___x_684_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_684_, 0, v___x_683_);
    lean_ctor_set(v___x_684_, 1, v___x_682_);
    lean_ctor_set(v___x_684_, 2, v___x_681_);
    lean_ctor_set(v___x_684_, 3, v___x_680_);
    lean_ctor_set(v___x_684_, 4, v___x_680_);
    return v___x_684_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommSemiring_default()
-> *mut LeanObject {
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    v___x_685_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommSemiring_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommSemiring_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommSemiring_default___closed__0,
    );
    return v___x_685_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommSemiring() -> *mut LeanObject
{
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    v___x_686_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommSemiring_default;
    return v___x_686_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1()
-> *mut LeanObject {
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    v___x_689_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_689_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__2()
-> *mut LeanObject {
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    v___x_690_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1,
    );
    v___x_691_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_691_, 0, v___x_690_);
    return v___x_691_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__3()
-> *mut LeanObject {
    let mut v___x_692_: u8 = 0;
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    v___x_692_ = 0;
    v___x_693_ = lean_unsigned_to_nat(0);
    v___x_694_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__2,
    );
    v___x_695_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__0;
    v___x_696_ = lean_alloc_ctor(0, 13, (1) as u32);
    lean_ctor_set(v___x_696_, 0, v___x_695_);
    lean_ctor_set(v___x_696_, 1, v___x_694_);
    lean_ctor_set(v___x_696_, 2, v___x_694_);
    lean_ctor_set(v___x_696_, 3, v___x_695_);
    lean_ctor_set(v___x_696_, 4, v___x_694_);
    lean_ctor_set(v___x_696_, 5, v___x_694_);
    lean_ctor_set(v___x_696_, 6, v___x_695_);
    lean_ctor_set(v___x_696_, 7, v___x_694_);
    lean_ctor_set(v___x_696_, 8, v___x_694_);
    lean_ctor_set(v___x_696_, 9, v___x_695_);
    lean_ctor_set(v___x_696_, 10, v___x_694_);
    lean_ctor_set(v___x_696_, 11, v___x_694_);
    lean_ctor_set(v___x_696_, 12, v___x_693_);
    lean_ctor_set_uint8(
        v___x_696_,
        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
        v___x_692_,
    );
    return v___x_696_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default() -> *mut LeanObject
{
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    v___x_697_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__3,
    );
    return v___x_697_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState() -> *mut LeanObject {
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    v___x_698_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default;
    return v___x_698_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_(
    mut v___x_699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    v___x_701_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_701_, 0, v___x_699_);
    return v___x_701_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2____boxed(
    mut v___x_702_: *mut LeanObject,
    mut v___y_703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_704_: *mut LeanObject = core::ptr::null_mut();
    v_res_704_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_(v___x_702_);
    return v_res_704_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_706_: *mut LeanObject = core::ptr::null_mut();
    v___x_705_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__3,
    );
    v___f_706_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_706_, 0, v___x_705_);
    return v___f_706_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    v___f_708_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_);
    v___x_709_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_708_);
    return v___x_709_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2____boxed(
    mut v_a_710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_711_: *mut LeanObject = core::ptr::null_mut();
    v_res_711_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_();
    return v_res_711_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(
    mut v_a_712_: *mut LeanObject,
    mut v_a_713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    v___x_715_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
    v___x_716_ =
        l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_715_, v_a_712_, v_a_713_);
    return v___x_716_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg___boxed(
    mut v_a_717_: *mut LeanObject,
    mut v_a_718_: *mut LeanObject,
    mut v_a_719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_720_: *mut LeanObject = core::ptr::null_mut();
    v_res_720_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_717_, v_a_718_);
    lean_dec_ref(v_a_718_);
    lean_dec(v_a_717_);
    return v_res_720_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_get_x27(
    mut v_a_721_: *mut LeanObject,
    mut v_a_722_: *mut LeanObject,
    mut v_a_723_: *mut LeanObject,
    mut v_a_724_: *mut LeanObject,
    mut v_a_725_: *mut LeanObject,
    mut v_a_726_: *mut LeanObject,
    mut v_a_727_: *mut LeanObject,
    mut v_a_728_: *mut LeanObject,
    mut v_a_729_: *mut LeanObject,
    mut v_a_730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    v___x_732_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_721_, v_a_729_);
    return v___x_732_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_get_x27___boxed(
    mut v_a_733_: *mut LeanObject,
    mut v_a_734_: *mut LeanObject,
    mut v_a_735_: *mut LeanObject,
    mut v_a_736_: *mut LeanObject,
    mut v_a_737_: *mut LeanObject,
    mut v_a_738_: *mut LeanObject,
    mut v_a_739_: *mut LeanObject,
    mut v_a_740_: *mut LeanObject,
    mut v_a_741_: *mut LeanObject,
    mut v_a_742_: *mut LeanObject,
    mut v_a_743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_744_: *mut LeanObject = core::ptr::null_mut();
    v_res_744_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27(
        v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_,
        v_a_742_,
    );
    lean_dec(v_a_742_);
    lean_dec_ref(v_a_741_);
    lean_dec(v_a_740_);
    lean_dec_ref(v_a_739_);
    lean_dec(v_a_738_);
    lean_dec_ref(v_a_737_);
    lean_dec(v_a_736_);
    lean_dec_ref(v_a_735_);
    lean_dec(v_a_734_);
    lean_dec(v_a_733_);
    return v_res_744_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_modify_x27___redArg(
    mut v_f_745_: *mut LeanObject,
    mut v_a_746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    v___x_748_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
    v___x_749_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_748_, v_f_745_, v_a_746_);
    return v___x_749_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_modify_x27___redArg___boxed(
    mut v_f_750_: *mut LeanObject,
    mut v_a_751_: *mut LeanObject,
    mut v_a_752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_753_: *mut LeanObject = core::ptr::null_mut();
    v_res_753_ = l_Lean_Meta_Grind_Arith_CommRing_modify_x27___redArg(v_f_750_, v_a_751_);
    lean_dec(v_a_751_);
    return v_res_753_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_modify_x27(
    mut v_f_754_: *mut LeanObject,
    mut v_a_755_: *mut LeanObject,
    mut v_a_756_: *mut LeanObject,
    mut v_a_757_: *mut LeanObject,
    mut v_a_758_: *mut LeanObject,
    mut v_a_759_: *mut LeanObject,
    mut v_a_760_: *mut LeanObject,
    mut v_a_761_: *mut LeanObject,
    mut v_a_762_: *mut LeanObject,
    mut v_a_763_: *mut LeanObject,
    mut v_a_764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    v___x_766_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
    v___x_767_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_766_, v_f_754_, v_a_755_);
    return v___x_767_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_modify_x27___boxed(
    mut v_f_768_: *mut LeanObject,
    mut v_a_769_: *mut LeanObject,
    mut v_a_770_: *mut LeanObject,
    mut v_a_771_: *mut LeanObject,
    mut v_a_772_: *mut LeanObject,
    mut v_a_773_: *mut LeanObject,
    mut v_a_774_: *mut LeanObject,
    mut v_a_775_: *mut LeanObject,
    mut v_a_776_: *mut LeanObject,
    mut v_a_777_: *mut LeanObject,
    mut v_a_778_: *mut LeanObject,
    mut v_a_779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_780_: *mut LeanObject = core::ptr::null_mut();
    v_res_780_ = l_Lean_Meta_Grind_Arith_CommRing_modify_x27(
        v_f_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_,
        v_a_777_, v_a_778_,
    );
    lean_dec(v_a_778_);
    lean_dec_ref(v_a_777_);
    lean_dec(v_a_776_);
    lean_dec_ref(v_a_775_);
    lean_dec(v_a_774_);
    lean_dec_ref(v_a_773_);
    lean_dec(v_a_772_);
    lean_dec_ref(v_a_771_);
    lean_dec(v_a_770_);
    lean_dec(v_a_769_);
    return v_res_780_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof);
    l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr);
    l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring_default);
    l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiring);
    l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing_default);
    l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRing);
    l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing_default);
    l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRing);
    l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommSemiring_default =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommSemiring_default();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommSemiring_default);
    l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommSemiring =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommSemiring();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommSemiring);
    l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default);
    l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Grind_Arith_CommRing_ringExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_ringExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Arith_Poly(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
}
