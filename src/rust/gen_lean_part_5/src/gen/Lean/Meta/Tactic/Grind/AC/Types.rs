// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.Types
// Imports: Init.Grind.AC Std.Data.HashMap Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.AC.Seq
use crate::ffi::{
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_lt, lean_uint64_mix_hash,
    lean_uint64_of_nat,
};
use crate::r#gen::Init::Grind::AC::{
    initialize_Init_Grind_AC, l_Lean_Grind_AC_instInhabitedExpr_default,
    l_Lean_Grind_AC_instInhabitedSeq_default, runtime_initialize_Init_Grind_AC,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::l_Lean_Expr_const___override;
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Seq::{
    initialize_Lean_Meta_Tactic_Grind_AC_Seq, l_Lean_Grind_AC_Seq_length,
    runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_registerSolverExtension___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Std::Data::HashMap::{
    initialize_Std_Data_HashMap, runtime_initialize_Std_Data_HashMap,
};
pub static l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_AC_instHashableExpr__lean: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_AC_instHashableSeq__lean: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0_value)
            as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstr: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instInhabitedStruct: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__0_value:
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
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instInhabitedState_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instInhabitedState: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_acExt: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(
    mut v_x_463_: *mut leanh::LeanObject,
) -> u64 {
    if leanh::lean_obj_tag(v_x_463_) == 0 {
        let mut v_x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_465_: u64 = 0;
        let mut v___x_466_: u64 = 0;
        let mut v___x_467_: u64 = 0;
        v_x_464_ = leanh::lean_ctor_get(v_x_463_, 0);
        v___x_465_ = 0u64;
        v___x_466_ = lean_uint64_of_nat(v_x_464_);
        v___x_467_ = lean_uint64_mix_hash(v___x_465_, v___x_466_);
        return v___x_467_;
    } else {
        let mut v_lhs_468_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_469_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_470_: u64 = 0;
        let mut v___x_471_: u64 = 0;
        let mut v___x_472_: u64 = 0;
        let mut v___x_473_: u64 = 0;
        let mut v___x_474_: u64 = 0;
        v_lhs_468_ = leanh::lean_ctor_get(v_x_463_, 0);
        v_rhs_469_ = leanh::lean_ctor_get(v_x_463_, 1);
        v___x_470_ = 1u64;
        v___x_471_ = l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(v_lhs_468_);
        v___x_472_ = lean_uint64_mix_hash(v___x_470_, v___x_471_);
        v___x_473_ = l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(v_rhs_469_);
        v___x_474_ = lean_uint64_mix_hash(v___x_472_, v___x_473_);
        return v___x_474_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash___boxed(
    mut v_x_475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_476_: u64 = 0;
    let mut v_r_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_476_ = l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(v_x_475_);
    leanh::lean_dec_ref(v_x_475_);
    v_r_477_ = leanh::lean_box_uint64(v_res_476_);
    return v_r_477_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(
    mut v_x_480_: *mut leanh::LeanObject,
) -> u64 {
    if leanh::lean_obj_tag(v_x_480_) == 0 {
        let mut v_x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_482_: u64 = 0;
        let mut v___x_483_: u64 = 0;
        let mut v___x_484_: u64 = 0;
        v_x_481_ = leanh::lean_ctor_get(v_x_480_, 0);
        v___x_482_ = 0u64;
        v___x_483_ = lean_uint64_of_nat(v_x_481_);
        v___x_484_ = lean_uint64_mix_hash(v___x_482_, v___x_483_);
        return v___x_484_;
    } else {
        let mut v_x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_s_486_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_487_: u64 = 0;
        let mut v___x_488_: u64 = 0;
        let mut v___x_489_: u64 = 0;
        let mut v___x_490_: u64 = 0;
        let mut v___x_491_: u64 = 0;
        v_x_485_ = leanh::lean_ctor_get(v_x_480_, 0);
        v_s_486_ = leanh::lean_ctor_get(v_x_480_, 1);
        v___x_487_ = 1u64;
        v___x_488_ = lean_uint64_of_nat(v_x_485_);
        v___x_489_ = lean_uint64_mix_hash(v___x_487_, v___x_488_);
        v___x_490_ = l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(v_s_486_);
        v___x_491_ = lean_uint64_mix_hash(v___x_489_, v___x_490_);
        return v___x_491_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash___boxed(
    mut v_x_492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_493_: u64 = 0;
    let mut v_r_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_493_ = l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(v_x_492_);
    leanh::lean_dec_ref(v_x_492_);
    v_r_494_ = leanh::lean_box_uint64(v_res_493_);
    return v_r_494_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx(
    mut v_x_497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_497_) {
        0 => {
            let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_498_ = leanh::lean_unsigned_to_nat(0);
            return v___x_498_;
        }
        1 => {
            let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_499_ = leanh::lean_unsigned_to_nat(1);
            return v___x_499_;
        }
        2 => {
            let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_500_ = leanh::lean_unsigned_to_nat(2);
            return v___x_500_;
        }
        3 => {
            let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_501_ = leanh::lean_unsigned_to_nat(3);
            return v___x_501_;
        }
        4 => {
            let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_502_ = leanh::lean_unsigned_to_nat(4);
            return v___x_502_;
        }
        5 => {
            let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_503_ = leanh::lean_unsigned_to_nat(5);
            return v___x_503_;
        }
        6 => {
            let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_504_ = leanh::lean_unsigned_to_nat(6);
            return v___x_504_;
        }
        7 => {
            let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_505_ = leanh::lean_unsigned_to_nat(7);
            return v___x_505_;
        }
        8 => {
            let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_506_ = leanh::lean_unsigned_to_nat(8);
            return v___x_506_;
        }
        9 => {
            let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_507_ = leanh::lean_unsigned_to_nat(9);
            return v___x_507_;
        }
        10 => {
            let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_508_ = leanh::lean_unsigned_to_nat(10);
            return v___x_508_;
        }
        11 => {
            let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_509_ = leanh::lean_unsigned_to_nat(11);
            return v___x_509_;
        }
        12 => {
            let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_510_ = leanh::lean_unsigned_to_nat(12);
            return v___x_510_;
        }
        13 => {
            let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_511_ = leanh::lean_unsigned_to_nat(13);
            return v___x_511_;
        }
        14 => {
            let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_512_ = leanh::lean_unsigned_to_nat(14);
            return v___x_512_;
        }
        15 => {
            let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_513_ = leanh::lean_unsigned_to_nat(15);
            return v___x_513_;
        }
        _ => {
            let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_514_ = leanh::lean_unsigned_to_nat(16);
            return v___x_514_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx___boxed(
    mut v_x_515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_516_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx(v_x_515_);
    leanh::lean_dec_ref(v_x_515_);
    return v_res_516_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
    mut v_t_517_: *mut leanh::LeanObject,
    mut v_k_518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_517_) {
        0 => {
            let mut v_a_519_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_520_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_ea_521_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_eb_522_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_519_ = leanh::lean_ctor_get(v_t_517_, 0);
            leanh::lean_inc_ref(v_a_519_);
            v_b_520_ = leanh::lean_ctor_get(v_t_517_, 1);
            leanh::lean_inc_ref(v_b_520_);
            v_ea_521_ = leanh::lean_ctor_get(v_t_517_, 2);
            leanh::lean_inc_ref(v_ea_521_);
            v_eb_522_ = leanh::lean_ctor_get(v_t_517_, 3);
            leanh::lean_inc_ref(v_eb_522_);
            leanh::lean_dec_ref_known(v_t_517_, 4);
            v___x_523_ =
                leanh::lean_apply_4(v_k_518_, v_a_519_, v_b_520_, v_ea_521_, v_eb_522_);
            return v___x_523_;
        }
        4 => {
            let mut v_lhs_524_: u8 = 0;
            let mut v_c_u2081_525_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_526_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lhs_524_ = leanh::lean_ctor_get_uint8(
                v_t_517_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            v_c_u2081_525_ = leanh::lean_ctor_get(v_t_517_, 0);
            leanh::lean_inc_ref(v_c_u2081_525_);
            v_c_u2082_526_ = leanh::lean_ctor_get(v_t_517_, 1);
            leanh::lean_inc_ref(v_c_u2082_526_);
            leanh::lean_dec_ref_known(v_t_517_, 2);
            v___x_527_ = leanh::lean_box((v_lhs_524_) as usize);
            v___x_528_ =
                leanh::lean_apply_3(v_k_518_, v___x_527_, v_c_u2081_525_, v_c_u2082_526_);
            return v___x_528_;
        }
        5 => {
            let mut v_lhs_529_: u8 = 0;
            let mut v_s_530_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_531_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_532_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lhs_529_ = leanh::lean_ctor_get_uint8(
                v_t_517_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
            );
            v_s_530_ = leanh::lean_ctor_get(v_t_517_, 0);
            leanh::lean_inc_ref(v_s_530_);
            v_c_u2081_531_ = leanh::lean_ctor_get(v_t_517_, 1);
            leanh::lean_inc_ref(v_c_u2081_531_);
            v_c_u2082_532_ = leanh::lean_ctor_get(v_t_517_, 2);
            leanh::lean_inc_ref(v_c_u2082_532_);
            leanh::lean_dec_ref_known(v_t_517_, 3);
            v___x_533_ = leanh::lean_box((v_lhs_529_) as usize);
            v___x_534_ = leanh::lean_apply_4(
                v_k_518_,
                v___x_533_,
                v_s_530_,
                v_c_u2081_531_,
                v_c_u2082_532_,
            );
            return v___x_534_;
        }
        6 => {
            let mut v_lhs_535_: u8 = 0;
            let mut v_s_536_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_537_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_538_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lhs_535_ = leanh::lean_ctor_get_uint8(
                v_t_517_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
            );
            v_s_536_ = leanh::lean_ctor_get(v_t_517_, 0);
            leanh::lean_inc_ref(v_s_536_);
            v_c_u2081_537_ = leanh::lean_ctor_get(v_t_517_, 1);
            leanh::lean_inc_ref(v_c_u2081_537_);
            v_c_u2082_538_ = leanh::lean_ctor_get(v_t_517_, 2);
            leanh::lean_inc_ref(v_c_u2082_538_);
            leanh::lean_dec_ref_known(v_t_517_, 3);
            v___x_539_ = leanh::lean_box((v_lhs_535_) as usize);
            v___x_540_ = leanh::lean_apply_4(
                v_k_518_,
                v___x_539_,
                v_s_536_,
                v_c_u2081_537_,
                v_c_u2082_538_,
            );
            return v___x_540_;
        }
        7 => {
            let mut v_lhs_541_: u8 = 0;
            let mut v_s_542_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_543_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_544_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lhs_541_ = leanh::lean_ctor_get_uint8(
                v_t_517_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
            );
            v_s_542_ = leanh::lean_ctor_get(v_t_517_, 0);
            leanh::lean_inc_ref(v_s_542_);
            v_c_u2081_543_ = leanh::lean_ctor_get(v_t_517_, 1);
            leanh::lean_inc_ref(v_c_u2081_543_);
            v_c_u2082_544_ = leanh::lean_ctor_get(v_t_517_, 2);
            leanh::lean_inc_ref(v_c_u2082_544_);
            leanh::lean_dec_ref_known(v_t_517_, 3);
            v___x_545_ = leanh::lean_box((v_lhs_541_) as usize);
            v___x_546_ = leanh::lean_apply_4(
                v_k_518_,
                v___x_545_,
                v_s_542_,
                v_c_u2081_543_,
                v_c_u2082_544_,
            );
            return v___x_546_;
        }
        8 => {
            let mut v_lhs_547_: u8 = 0;
            let mut v_s_u2081_548_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_u2082_549_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_550_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_551_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lhs_547_ = leanh::lean_ctor_get_uint8(
                v_t_517_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
            );
            v_s_u2081_548_ = leanh::lean_ctor_get(v_t_517_, 0);
            leanh::lean_inc_ref(v_s_u2081_548_);
            v_s_u2082_549_ = leanh::lean_ctor_get(v_t_517_, 1);
            leanh::lean_inc_ref(v_s_u2082_549_);
            v_c_u2081_550_ = leanh::lean_ctor_get(v_t_517_, 2);
            leanh::lean_inc_ref(v_c_u2081_550_);
            v_c_u2082_551_ = leanh::lean_ctor_get(v_t_517_, 3);
            leanh::lean_inc_ref(v_c_u2082_551_);
            leanh::lean_dec_ref_known(v_t_517_, 4);
            v___x_552_ = leanh::lean_box((v_lhs_547_) as usize);
            v___x_553_ = leanh::lean_apply_5(
                v_k_518_,
                v___x_552_,
                v_s_u2081_548_,
                v_s_u2082_549_,
                v_c_u2081_550_,
                v_c_u2082_551_,
            );
            return v___x_553_;
        }
        9 => {
            let mut v_r_u2081_554_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_555_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_u2082_556_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_557_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_558_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_r_u2081_554_ = leanh::lean_ctor_get(v_t_517_, 0);
            leanh::lean_inc_ref(v_r_u2081_554_);
            v_c_555_ = leanh::lean_ctor_get(v_t_517_, 1);
            leanh::lean_inc_ref(v_c_555_);
            v_r_u2082_556_ = leanh::lean_ctor_get(v_t_517_, 2);
            leanh::lean_inc_ref(v_r_u2082_556_);
            v_c_u2081_557_ = leanh::lean_ctor_get(v_t_517_, 3);
            leanh::lean_inc_ref(v_c_u2081_557_);
            v_c_u2082_558_ = leanh::lean_ctor_get(v_t_517_, 4);
            leanh::lean_inc_ref(v_c_u2082_558_);
            leanh::lean_dec_ref_known(v_t_517_, 5);
            v___x_559_ = leanh::lean_apply_5(
                v_k_518_,
                v_r_u2081_554_,
                v_c_555_,
                v_r_u2082_556_,
                v_c_u2081_557_,
                v_c_u2082_558_,
            );
            return v___x_559_;
        }
        10 => {
            let mut v_p_560_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_561_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_562_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_563_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_564_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_p_560_ = leanh::lean_ctor_get(v_t_517_, 0);
            leanh::lean_inc_ref(v_p_560_);
            v_s_561_ = leanh::lean_ctor_get(v_t_517_, 1);
            leanh::lean_inc_ref(v_s_561_);
            v_c_562_ = leanh::lean_ctor_get(v_t_517_, 2);
            leanh::lean_inc_ref(v_c_562_);
            v_c_u2081_563_ = leanh::lean_ctor_get(v_t_517_, 3);
            leanh::lean_inc_ref(v_c_u2081_563_);
            v_c_u2082_564_ = leanh::lean_ctor_get(v_t_517_, 4);
            leanh::lean_inc_ref(v_c_u2082_564_);
            leanh::lean_dec_ref_known(v_t_517_, 5);
            v___x_565_ = leanh::lean_apply_5(
                v_k_518_,
                v_p_560_,
                v_s_561_,
                v_c_562_,
                v_c_u2081_563_,
                v_c_u2082_564_,
            );
            return v___x_565_;
        }
        11 => {
            let mut v_x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_567_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_x_566_ = leanh::lean_ctor_get(v_t_517_, 0);
            leanh::lean_inc(v_x_566_);
            v_c_u2081_567_ = leanh::lean_ctor_get(v_t_517_, 1);
            leanh::lean_inc_ref(v_c_u2081_567_);
            leanh::lean_dec_ref_known(v_t_517_, 2);
            v___x_568_ = leanh::lean_apply_2(v_k_518_, v_x_566_, v_c_u2081_567_);
            return v___x_568_;
        }
        12 => {
            let mut v_x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_570_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_x_569_ = leanh::lean_ctor_get(v_t_517_, 0);
            leanh::lean_inc(v_x_569_);
            v_c_u2081_570_ = leanh::lean_ctor_get(v_t_517_, 1);
            leanh::lean_inc_ref(v_c_u2081_570_);
            leanh::lean_dec_ref_known(v_t_517_, 2);
            v___x_571_ = leanh::lean_apply_2(v_k_518_, v_x_569_, v_c_u2081_570_);
            return v___x_571_;
        }
        13 => {
            let mut v_x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_573_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_x_572_ = leanh::lean_ctor_get(v_t_517_, 0);
            leanh::lean_inc(v_x_572_);
            v_c_u2081_573_ = leanh::lean_ctor_get(v_t_517_, 1);
            leanh::lean_inc_ref(v_c_u2081_573_);
            leanh::lean_dec_ref_known(v_t_517_, 2);
            v___x_574_ = leanh::lean_apply_2(v_k_518_, v_x_572_, v_c_u2081_573_);
            return v___x_574_;
        }
        _ => {
            let mut v_c_575_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_c_575_ = leanh::lean_ctor_get(v_t_517_, 0);
            leanh::lean_inc_ref(v_c_575_);
            leanh::lean_dec_ref(v_t_517_);
            v___x_576_ = leanh::lean_apply_1(v_k_518_, v_c_575_);
            return v___x_576_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim(
    mut v_motive__2_577_: *mut leanh::LeanObject,
    mut v_ctorIdx_578_: *mut leanh::LeanObject,
    mut v_t_579_: *mut leanh::LeanObject,
    mut v_h_580_: *mut leanh::LeanObject,
    mut v_k_581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_582_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_579_, v_k_581_);
    return v___x_582_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___boxed(
    mut v_motive__2_583_: *mut leanh::LeanObject,
    mut v_ctorIdx_584_: *mut leanh::LeanObject,
    mut v_t_585_: *mut leanh::LeanObject,
    mut v_h_586_: *mut leanh::LeanObject,
    mut v_k_587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_588_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim(
        v_motive__2_583_,
        v_ctorIdx_584_,
        v_t_585_,
        v_h_586_,
        v_k_587_,
    );
    leanh::lean_dec(v_ctorIdx_584_);
    return v_res_588_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_core_elim___redArg(
    mut v_t_589_: *mut leanh::LeanObject,
    mut v_core_590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_591_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_589_, v_core_590_);
    return v___x_591_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_core_elim(
    mut v_motive__2_592_: *mut leanh::LeanObject,
    mut v_t_593_: *mut leanh::LeanObject,
    mut v_h_594_: *mut leanh::LeanObject,
    mut v_core_595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_596_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_593_, v_core_595_);
    return v___x_596_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup_elim___redArg(
    mut v_t_597_: *mut leanh::LeanObject,
    mut v_erase__dup_598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_599_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_597_, v_erase__dup_598_);
    return v___x_599_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup_elim(
    mut v_motive__2_600_: *mut leanh::LeanObject,
    mut v_t_601_: *mut leanh::LeanObject,
    mut v_h_602_: *mut leanh::LeanObject,
    mut v_erase__dup_603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_604_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_601_, v_erase__dup_603_);
    return v___x_604_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase0_elim___redArg(
    mut v_t_605_: *mut leanh::LeanObject,
    mut v_erase0_606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_607_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_605_, v_erase0_606_);
    return v___x_607_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase0_elim(
    mut v_motive__2_608_: *mut leanh::LeanObject,
    mut v_t_609_: *mut leanh::LeanObject,
    mut v_h_610_: *mut leanh::LeanObject,
    mut v_erase0_611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_612_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_609_, v_erase0_611_);
    return v___x_612_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_swap_elim___redArg(
    mut v_t_613_: *mut leanh::LeanObject,
    mut v_swap_614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_615_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_613_, v_swap_614_);
    return v___x_615_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_swap_elim(
    mut v_motive__2_616_: *mut leanh::LeanObject,
    mut v_t_617_: *mut leanh::LeanObject,
    mut v_h_618_: *mut leanh::LeanObject,
    mut v_swap_619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_620_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_617_, v_swap_619_);
    return v___x_620_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__exact_elim___redArg(
    mut v_t_621_: *mut leanh::LeanObject,
    mut v_simp__exact_622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_623_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_621_, v_simp__exact_622_);
    return v___x_623_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__exact_elim(
    mut v_motive__2_624_: *mut leanh::LeanObject,
    mut v_t_625_: *mut leanh::LeanObject,
    mut v_h_626_: *mut leanh::LeanObject,
    mut v_simp__exact_627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_628_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_625_, v_simp__exact_627_);
    return v___x_628_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__ac_elim___redArg(
    mut v_t_629_: *mut leanh::LeanObject,
    mut v_simp__ac_630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_631_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_629_, v_simp__ac_630_);
    return v___x_631_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__ac_elim(
    mut v_motive__2_632_: *mut leanh::LeanObject,
    mut v_t_633_: *mut leanh::LeanObject,
    mut v_h_634_: *mut leanh::LeanObject,
    mut v_simp__ac_635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_636_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_633_, v_simp__ac_635_);
    return v___x_636_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__suffix_elim___redArg(
    mut v_t_637_: *mut leanh::LeanObject,
    mut v_simp__suffix_638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_639_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_637_, v_simp__suffix_638_);
    return v___x_639_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__suffix_elim(
    mut v_motive__2_640_: *mut leanh::LeanObject,
    mut v_t_641_: *mut leanh::LeanObject,
    mut v_h_642_: *mut leanh::LeanObject,
    mut v_simp__suffix_643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_644_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_641_, v_simp__suffix_643_);
    return v___x_644_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__prefix_elim___redArg(
    mut v_t_645_: *mut leanh::LeanObject,
    mut v_simp__prefix_646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_647_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_645_, v_simp__prefix_646_);
    return v___x_647_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__prefix_elim(
    mut v_motive__2_648_: *mut leanh::LeanObject,
    mut v_t_649_: *mut leanh::LeanObject,
    mut v_h_650_: *mut leanh::LeanObject,
    mut v_simp__prefix_651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_652_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_649_, v_simp__prefix_651_);
    return v___x_652_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__middle_elim___redArg(
    mut v_t_653_: *mut leanh::LeanObject,
    mut v_simp__middle_654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_655_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_653_, v_simp__middle_654_);
    return v___x_655_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__middle_elim(
    mut v_motive__2_656_: *mut leanh::LeanObject,
    mut v_t_657_: *mut leanh::LeanObject,
    mut v_h_658_: *mut leanh::LeanObject,
    mut v_simp__middle_659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_660_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_657_, v_simp__middle_659_);
    return v___x_660_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac_elim___redArg(
    mut v_t_661_: *mut leanh::LeanObject,
    mut v_superpose__ac_662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_663_ =
        l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_661_, v_superpose__ac_662_);
    return v___x_663_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac_elim(
    mut v_motive__2_664_: *mut leanh::LeanObject,
    mut v_t_665_: *mut leanh::LeanObject,
    mut v_h_666_: *mut leanh::LeanObject,
    mut v_superpose__ac_667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_668_ =
        l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_665_, v_superpose__ac_667_);
    return v___x_668_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose_elim___redArg(
    mut v_t_669_: *mut leanh::LeanObject,
    mut v_superpose_670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_671_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_669_, v_superpose_670_);
    return v___x_671_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose_elim(
    mut v_motive__2_672_: *mut leanh::LeanObject,
    mut v_t_673_: *mut leanh::LeanObject,
    mut v_h_674_: *mut leanh::LeanObject,
    mut v_superpose_675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_676_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_673_, v_superpose_675_);
    return v___x_676_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac__idempotent_elim___redArg(
    mut v_t_677_: *mut leanh::LeanObject,
    mut v_superpose__ac__idempotent_678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_679_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
        v_t_677_,
        v_superpose__ac__idempotent_678_,
    );
    return v___x_679_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac__idempotent_elim(
    mut v_motive__2_680_: *mut leanh::LeanObject,
    mut v_t_681_: *mut leanh::LeanObject,
    mut v_h_682_: *mut leanh::LeanObject,
    mut v_superpose__ac__idempotent_683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_684_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
        v_t_681_,
        v_superpose__ac__idempotent_683_,
    );
    return v___x_684_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__head__idempotent_elim___redArg(
    mut v_t_685_: *mut leanh::LeanObject,
    mut v_superpose__head__idempotent_686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_687_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
        v_t_685_,
        v_superpose__head__idempotent_686_,
    );
    return v___x_687_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__head__idempotent_elim(
    mut v_motive__2_688_: *mut leanh::LeanObject,
    mut v_t_689_: *mut leanh::LeanObject,
    mut v_h_690_: *mut leanh::LeanObject,
    mut v_superpose__head__idempotent_691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_692_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
        v_t_689_,
        v_superpose__head__idempotent_691_,
    );
    return v___x_692_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__tail__idempotent_elim___redArg(
    mut v_t_693_: *mut leanh::LeanObject,
    mut v_superpose__tail__idempotent_694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_695_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
        v_t_693_,
        v_superpose__tail__idempotent_694_,
    );
    return v___x_695_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__tail__idempotent_elim(
    mut v_motive__2_696_: *mut leanh::LeanObject,
    mut v_t_697_: *mut leanh::LeanObject,
    mut v_h_698_: *mut leanh::LeanObject,
    mut v_superpose__tail__idempotent_699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_700_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
        v_t_697_,
        v_superpose__tail__idempotent_699_,
    );
    return v___x_700_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_refl_elim___redArg(
    mut v_t_701_: *mut leanh::LeanObject,
    mut v_refl_702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_703_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_701_, v_refl_702_);
    return v___x_703_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_refl_elim(
    mut v_motive__2_704_: *mut leanh::LeanObject,
    mut v_t_705_: *mut leanh::LeanObject,
    mut v_h_706_: *mut leanh::LeanObject,
    mut v_refl_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_708_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_705_, v_refl_707_);
    return v___x_708_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup__rhs_elim___redArg(
    mut v_t_709_: *mut leanh::LeanObject,
    mut v_erase__dup__rhs_710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_711_ =
        l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_709_, v_erase__dup__rhs_710_);
    return v___x_711_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup__rhs_elim(
    mut v_motive__2_712_: *mut leanh::LeanObject,
    mut v_t_713_: *mut leanh::LeanObject,
    mut v_h_714_: *mut leanh::LeanObject,
    mut v_erase__dup__rhs_715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_716_ =
        l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_713_, v_erase__dup__rhs_715_);
    return v___x_716_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase0__rhs_elim___redArg(
    mut v_t_717_: *mut leanh::LeanObject,
    mut v_erase0__rhs_718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_719_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_717_, v_erase0__rhs_718_);
    return v___x_719_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase0__rhs_elim(
    mut v_motive__2_720_: *mut leanh::LeanObject,
    mut v_t_721_: *mut leanh::LeanObject,
    mut v_h_722_: *mut leanh::LeanObject,
    mut v_erase0__rhs_723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_724_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_721_, v_erase0__rhs_723_);
    return v___x_724_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_728_ = leanh::lean_box(0);
    v___x_729_ = l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1;
    v___x_730_ = l_Lean_Expr_const___override(v___x_729_, v___x_728_);
    return v___x_730_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_731_ = l_Lean_Grind_AC_instInhabitedExpr_default;
    v___x_732_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2,
    );
    v___x_733_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_733_, 0, v___x_732_);
    leanh::lean_ctor_set(v___x_733_, 1, v___x_732_);
    leanh::lean_ctor_set(v___x_733_, 2, v___x_731_);
    leanh::lean_ctor_set(v___x_733_, 3, v___x_731_);
    return v___x_733_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof() -> *mut leanh::LeanObject
{
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_734_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3,
    );
    return v___x_734_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_735_ = leanh::lean_unsigned_to_nat(0);
    v___x_736_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3,
    );
    v___x_737_ = l_Lean_Grind_AC_instInhabitedSeq_default;
    v___x_738_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_738_, 0, v___x_737_);
    leanh::lean_ctor_set(v___x_738_, 1, v___x_737_);
    leanh::lean_ctor_set(v___x_738_, 2, v___x_736_);
    leanh::lean_ctor_set(v___x_738_, 3, v___x_735_);
    return v___x_738_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr() -> *mut leanh::LeanObject {
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_739_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0,
    );
    return v___x_739_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_compare(
    mut v_c_u2081_740_: *mut leanh::LeanObject,
    mut v_c_u2082_741_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_lhs_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: u8 = 0;
    v_lhs_742_ = leanh::lean_ctor_get(v_c_u2081_740_, 0);
    v_id_743_ = leanh::lean_ctor_get(v_c_u2081_740_, 3);
    v_lhs_744_ = leanh::lean_ctor_get(v_c_u2082_741_, 0);
    v_id_745_ = leanh::lean_ctor_get(v_c_u2082_741_, 3);
    v___x_746_ = l_Lean_Grind_AC_Seq_length(v_lhs_742_);
    v___x_747_ = l_Lean_Grind_AC_Seq_length(v_lhs_744_);
    v___x_748_ = lean_nat_dec_lt(v___x_746_, v___x_747_);
    if v___x_748_ == 0 {
        let mut v___x_749_: u8 = 0;
        v___x_749_ = lean_nat_dec_eq(v___x_746_, v___x_747_);
        leanh::lean_dec(v___x_747_);
        leanh::lean_dec(v___x_746_);
        if v___x_749_ == 0 {
            let mut v___x_750_: u8 = 0;
            v___x_750_ = 2;
            return v___x_750_;
        } else {
            let mut v___x_751_: u8 = 0;
            v___x_751_ = lean_nat_dec_lt(v_id_743_, v_id_745_);
            if v___x_751_ == 0 {
                let mut v___x_752_: u8 = 0;
                v___x_752_ = lean_nat_dec_eq(v_id_743_, v_id_745_);
                if v___x_752_ == 0 {
                    let mut v___x_753_: u8 = 0;
                    v___x_753_ = 2;
                    return v___x_753_;
                } else {
                    let mut v___x_754_: u8 = 0;
                    v___x_754_ = 1;
                    return v___x_754_;
                }
            } else {
                let mut v___x_755_: u8 = 0;
                v___x_755_ = 0;
                return v___x_755_;
            }
        }
    } else {
        let mut v___x_756_: u8 = 0;
        leanh::lean_dec(v___x_747_);
        leanh::lean_dec(v___x_746_);
        v___x_756_ = 0;
        return v___x_756_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_compare___boxed(
    mut v_c_u2081_757_: *mut leanh::LeanObject,
    mut v_c_u2082_758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_759_: u8 = 0;
    let mut v_r_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_759_ = l_Lean_Meta_Grind_AC_EqCnstr_compare(v_c_u2081_757_, v_c_u2082_758_);
    leanh::lean_dec_ref(v_c_u2082_758_);
    leanh::lean_dec_ref(v_c_u2081_757_);
    v_r_760_ = leanh::lean_box((v_res_759_) as usize);
    return v_r_760_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx(
    mut v_x_761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_761_) {
        0 => {
            let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_762_ = leanh::lean_unsigned_to_nat(0);
            return v___x_762_;
        }
        1 => {
            let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_763_ = leanh::lean_unsigned_to_nat(1);
            return v___x_763_;
        }
        2 => {
            let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_764_ = leanh::lean_unsigned_to_nat(2);
            return v___x_764_;
        }
        3 => {
            let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_765_ = leanh::lean_unsigned_to_nat(3);
            return v___x_765_;
        }
        4 => {
            let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_766_ = leanh::lean_unsigned_to_nat(4);
            return v___x_766_;
        }
        5 => {
            let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_767_ = leanh::lean_unsigned_to_nat(5);
            return v___x_767_;
        }
        6 => {
            let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_768_ = leanh::lean_unsigned_to_nat(6);
            return v___x_768_;
        }
        _ => {
            let mut v___x_769_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_769_ = leanh::lean_unsigned_to_nat(7);
            return v___x_769_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx___boxed(
    mut v_x_770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_771_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx(v_x_770_);
    leanh::lean_dec_ref(v_x_770_);
    return v_res_771_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(
    mut v_t_772_: *mut leanh::LeanObject,
    mut v_k_773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_772_) {
        0 => {
            let mut v_a_774_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_775_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_ea_776_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_eb_777_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_774_ = leanh::lean_ctor_get(v_t_772_, 0);
            leanh::lean_inc_ref(v_a_774_);
            v_b_775_ = leanh::lean_ctor_get(v_t_772_, 1);
            leanh::lean_inc_ref(v_b_775_);
            v_ea_776_ = leanh::lean_ctor_get(v_t_772_, 2);
            leanh::lean_inc_ref(v_ea_776_);
            v_eb_777_ = leanh::lean_ctor_get(v_t_772_, 3);
            leanh::lean_inc_ref(v_eb_777_);
            leanh::lean_dec_ref_known(v_t_772_, 4);
            v___x_778_ =
                leanh::lean_apply_4(v_k_773_, v_a_774_, v_b_775_, v_ea_776_, v_eb_777_);
            return v___x_778_;
        }
        1 => {
            let mut v_c_779_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_c_779_ = leanh::lean_ctor_get(v_t_772_, 0);
            leanh::lean_inc_ref(v_c_779_);
            leanh::lean_dec_ref_known(v_t_772_, 1);
            v___x_780_ = leanh::lean_apply_1(v_k_773_, v_c_779_);
            return v___x_780_;
        }
        2 => {
            let mut v_c_781_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_782_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_c_781_ = leanh::lean_ctor_get(v_t_772_, 0);
            leanh::lean_inc_ref(v_c_781_);
            leanh::lean_dec_ref_known(v_t_772_, 1);
            v___x_782_ = leanh::lean_apply_1(v_k_773_, v_c_781_);
            return v___x_782_;
        }
        3 => {
            let mut v_lhs_783_: u8 = 0;
            let mut v_c_u2081_784_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_785_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_786_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lhs_783_ = leanh::lean_ctor_get_uint8(
                v_t_772_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            v_c_u2081_784_ = leanh::lean_ctor_get(v_t_772_, 0);
            leanh::lean_inc_ref(v_c_u2081_784_);
            v_c_u2082_785_ = leanh::lean_ctor_get(v_t_772_, 1);
            leanh::lean_inc_ref(v_c_u2082_785_);
            leanh::lean_dec_ref_known(v_t_772_, 2);
            v___x_786_ = leanh::lean_box((v_lhs_783_) as usize);
            v___x_787_ =
                leanh::lean_apply_3(v_k_773_, v___x_786_, v_c_u2081_784_, v_c_u2082_785_);
            return v___x_787_;
        }
        7 => {
            let mut v_lhs_788_: u8 = 0;
            let mut v_s_u2081_789_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_u2082_790_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_791_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_792_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lhs_788_ = leanh::lean_ctor_get_uint8(
                v_t_772_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
            );
            v_s_u2081_789_ = leanh::lean_ctor_get(v_t_772_, 0);
            leanh::lean_inc_ref(v_s_u2081_789_);
            v_s_u2082_790_ = leanh::lean_ctor_get(v_t_772_, 1);
            leanh::lean_inc_ref(v_s_u2082_790_);
            v_c_u2081_791_ = leanh::lean_ctor_get(v_t_772_, 2);
            leanh::lean_inc_ref(v_c_u2081_791_);
            v_c_u2082_792_ = leanh::lean_ctor_get(v_t_772_, 3);
            leanh::lean_inc_ref(v_c_u2082_792_);
            leanh::lean_dec_ref_known(v_t_772_, 4);
            v___x_793_ = leanh::lean_box((v_lhs_788_) as usize);
            v___x_794_ = leanh::lean_apply_5(
                v_k_773_,
                v___x_793_,
                v_s_u2081_789_,
                v_s_u2082_790_,
                v_c_u2081_791_,
                v_c_u2082_792_,
            );
            return v___x_794_;
        }
        _ => {
            let mut v_lhs_795_: u8 = 0;
            let mut v_s_796_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_797_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_798_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_799_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lhs_795_ = leanh::lean_ctor_get_uint8(
                v_t_772_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
            );
            v_s_796_ = leanh::lean_ctor_get(v_t_772_, 0);
            leanh::lean_inc_ref(v_s_796_);
            v_c_u2081_797_ = leanh::lean_ctor_get(v_t_772_, 1);
            leanh::lean_inc_ref(v_c_u2081_797_);
            v_c_u2082_798_ = leanh::lean_ctor_get(v_t_772_, 2);
            leanh::lean_inc_ref(v_c_u2082_798_);
            leanh::lean_dec_ref(v_t_772_);
            v___x_799_ = leanh::lean_box((v_lhs_795_) as usize);
            v___x_800_ = leanh::lean_apply_4(
                v_k_773_,
                v___x_799_,
                v_s_796_,
                v_c_u2081_797_,
                v_c_u2082_798_,
            );
            return v___x_800_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim(
    mut v_motive__2_801_: *mut leanh::LeanObject,
    mut v_ctorIdx_802_: *mut leanh::LeanObject,
    mut v_t_803_: *mut leanh::LeanObject,
    mut v_h_804_: *mut leanh::LeanObject,
    mut v_k_805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_806_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_803_, v_k_805_);
    return v___x_806_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___boxed(
    mut v_motive__2_807_: *mut leanh::LeanObject,
    mut v_ctorIdx_808_: *mut leanh::LeanObject,
    mut v_t_809_: *mut leanh::LeanObject,
    mut v_h_810_: *mut leanh::LeanObject,
    mut v_k_811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_812_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim(
        v_motive__2_807_,
        v_ctorIdx_808_,
        v_t_809_,
        v_h_810_,
        v_k_811_,
    );
    leanh::lean_dec(v_ctorIdx_808_);
    return v_res_812_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_core_elim___redArg(
    mut v_t_813_: *mut leanh::LeanObject,
    mut v_core_814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_815_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_813_, v_core_814_);
    return v___x_815_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_core_elim(
    mut v_motive__2_816_: *mut leanh::LeanObject,
    mut v_t_817_: *mut leanh::LeanObject,
    mut v_h_818_: *mut leanh::LeanObject,
    mut v_core_819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_820_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_817_, v_core_819_);
    return v___x_820_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase__dup_elim___redArg(
    mut v_t_821_: *mut leanh::LeanObject,
    mut v_erase__dup_822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_823_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_821_, v_erase__dup_822_);
    return v___x_823_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase__dup_elim(
    mut v_motive__2_824_: *mut leanh::LeanObject,
    mut v_t_825_: *mut leanh::LeanObject,
    mut v_h_826_: *mut leanh::LeanObject,
    mut v_erase__dup_827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_828_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_825_, v_erase__dup_827_);
    return v___x_828_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase0_elim___redArg(
    mut v_t_829_: *mut leanh::LeanObject,
    mut v_erase0_830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_829_, v_erase0_830_);
    return v___x_831_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase0_elim(
    mut v_motive__2_832_: *mut leanh::LeanObject,
    mut v_t_833_: *mut leanh::LeanObject,
    mut v_h_834_: *mut leanh::LeanObject,
    mut v_erase0_835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_836_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_833_, v_erase0_835_);
    return v___x_836_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__exact_elim___redArg(
    mut v_t_837_: *mut leanh::LeanObject,
    mut v_simp__exact_838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_839_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_837_, v_simp__exact_838_);
    return v___x_839_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__exact_elim(
    mut v_motive__2_840_: *mut leanh::LeanObject,
    mut v_t_841_: *mut leanh::LeanObject,
    mut v_h_842_: *mut leanh::LeanObject,
    mut v_simp__exact_843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_844_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_841_, v_simp__exact_843_);
    return v___x_844_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__ac_elim___redArg(
    mut v_t_845_: *mut leanh::LeanObject,
    mut v_simp__ac_846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_847_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_845_, v_simp__ac_846_);
    return v___x_847_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__ac_elim(
    mut v_motive__2_848_: *mut leanh::LeanObject,
    mut v_t_849_: *mut leanh::LeanObject,
    mut v_h_850_: *mut leanh::LeanObject,
    mut v_simp__ac_851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_852_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_849_, v_simp__ac_851_);
    return v___x_852_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__suffix_elim___redArg(
    mut v_t_853_: *mut leanh::LeanObject,
    mut v_simp__suffix_854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_855_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_853_, v_simp__suffix_854_);
    return v___x_855_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__suffix_elim(
    mut v_motive__2_856_: *mut leanh::LeanObject,
    mut v_t_857_: *mut leanh::LeanObject,
    mut v_h_858_: *mut leanh::LeanObject,
    mut v_simp__suffix_859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_860_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_857_, v_simp__suffix_859_);
    return v___x_860_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__prefix_elim___redArg(
    mut v_t_861_: *mut leanh::LeanObject,
    mut v_simp__prefix_862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_863_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_861_, v_simp__prefix_862_);
    return v___x_863_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__prefix_elim(
    mut v_motive__2_864_: *mut leanh::LeanObject,
    mut v_t_865_: *mut leanh::LeanObject,
    mut v_h_866_: *mut leanh::LeanObject,
    mut v_simp__prefix_867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_868_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_865_, v_simp__prefix_867_);
    return v___x_868_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__middle_elim___redArg(
    mut v_t_869_: *mut leanh::LeanObject,
    mut v_simp__middle_870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_871_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_869_, v_simp__middle_870_);
    return v___x_871_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__middle_elim(
    mut v_motive__2_872_: *mut leanh::LeanObject,
    mut v_t_873_: *mut leanh::LeanObject,
    mut v_h_874_: *mut leanh::LeanObject,
    mut v_simp__middle_875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_876_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_873_, v_simp__middle_875_);
    return v___x_876_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_877_ = leanh::lean_unsigned_to_nat(32);
    v___x_878_ = lean_mk_empty_array_with_capacity(v___x_877_);
    v___x_879_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_879_, 0, v___x_878_);
    return v___x_879_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_880_: usize = 0;
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_880_ = 5usize;
    v___x_881_ = leanh::lean_unsigned_to_nat(0);
    v___x_882_ = leanh::lean_unsigned_to_nat(32);
    v___x_883_ = lean_mk_empty_array_with_capacity(v___x_882_);
    v___x_884_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0,
    );
    v___x_885_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_885_, 0, v___x_884_);
    leanh::lean_ctor_set(v___x_885_, 1, v___x_883_);
    leanh::lean_ctor_set(v___x_885_, 2, v___x_881_);
    leanh::lean_ctor_set(v___x_885_, 3, v___x_881_);
    leanh::lean_ctor_set_usize(v___x_885_, 4, v___x_880_);
    return v___x_885_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_886_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_886_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_887_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2,
    );
    v___x_888_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_888_, 0, v___x_887_);
    return v___x_888_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_889_: u8 = 0;
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_889_ = 0;
    v___x_890_ = leanh::lean_box(0);
    v___x_891_ = leanh::lean_box(1);
    v___x_892_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3,
    );
    v___x_893_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1,
    );
    v___x_894_ = leanh::lean_box(0);
    v___x_895_ = leanh::lean_box(0);
    v___x_896_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2,
    );
    v___x_897_ = leanh::lean_unsigned_to_nat(0);
    v___x_898_ = leanh::lean_alloc_ctor(0, 17, (1) as u32);
    leanh::lean_ctor_set(v___x_898_, 0, v___x_897_);
    leanh::lean_ctor_set(v___x_898_, 1, v___x_896_);
    leanh::lean_ctor_set(v___x_898_, 2, v___x_895_);
    leanh::lean_ctor_set(v___x_898_, 3, v___x_896_);
    leanh::lean_ctor_set(v___x_898_, 4, v___x_894_);
    leanh::lean_ctor_set(v___x_898_, 5, v___x_896_);
    leanh::lean_ctor_set(v___x_898_, 6, v___x_894_);
    leanh::lean_ctor_set(v___x_898_, 7, v___x_894_);
    leanh::lean_ctor_set(v___x_898_, 8, v___x_894_);
    leanh::lean_ctor_set(v___x_898_, 9, v___x_897_);
    leanh::lean_ctor_set(v___x_898_, 10, v___x_893_);
    leanh::lean_ctor_set(v___x_898_, 11, v___x_892_);
    leanh::lean_ctor_set(v___x_898_, 12, v___x_892_);
    leanh::lean_ctor_set(v___x_898_, 13, v___x_893_);
    leanh::lean_ctor_set(v___x_898_, 14, v___x_891_);
    leanh::lean_ctor_set(v___x_898_, 15, v___x_890_);
    leanh::lean_ctor_set(v___x_898_, 16, v___x_893_);
    leanh::lean_ctor_set_uint8(
        v___x_898_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
        v___x_889_,
    );
    return v___x_898_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default()
-> *mut leanh::LeanObject {
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_899_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4,
    );
    return v___x_899_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct() -> *mut leanh::LeanObject {
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_900_ = l_Lean_Meta_Grind_AC_instInhabitedStruct_default;
    return v___x_900_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_903_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_903_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_904_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1,
    );
    v___x_905_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_905_, 0, v___x_904_);
    return v___x_905_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_906_ = leanh::lean_unsigned_to_nat(0);
    v___x_907_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2,
    );
    v___x_908_ = l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__0;
    v___x_909_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_909_, 0, v___x_908_);
    leanh::lean_ctor_set(v___x_909_, 1, v___x_907_);
    leanh::lean_ctor_set(v___x_909_, 2, v___x_907_);
    leanh::lean_ctor_set(v___x_909_, 3, v___x_906_);
    return v___x_909_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedState_default()
-> *mut leanh::LeanObject {
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_910_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3,
    );
    return v___x_910_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedState() -> *mut leanh::LeanObject {
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_911_ = l_Lean_Meta_Grind_AC_instInhabitedState_default;
    return v___x_911_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(
    mut v___x_912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_914_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_914_, 0, v___x_912_);
    return v___x_914_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed(
    mut v___x_915_: *mut leanh::LeanObject,
    mut v___y_916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_917_ = l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(v___x_915_);
    return v_res_917_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_918_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3,
    );
    v___f_919_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_919_, 0, v___x_918_);
    return v___f_919_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_921_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_);
    v___x_922_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_921_);
    return v___x_922_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed(
    mut v_a_923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_924_ = l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_();
    return v_res_924_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_AC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof =
        _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof);
    l_Lean_Meta_Grind_AC_instInhabitedEqCnstr = _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedEqCnstr);
    l_Lean_Meta_Grind_AC_instInhabitedStruct_default =
        _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedStruct_default);
    l_Lean_Meta_Grind_AC_instInhabitedStruct = _init_l_Lean_Meta_Grind_AC_instInhabitedStruct();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedStruct);
    l_Lean_Meta_Grind_AC_instInhabitedState_default =
        _init_l_Lean_Meta_Grind_AC_instInhabitedState_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedState_default);
    l_Lean_Meta_Grind_AC_instInhabitedState = _init_l_Lean_Meta_Grind_AC_instInhabitedState();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedState);
    res = l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Grind_AC_acExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_AC_acExt);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_AC_Types(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_AC_Types(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_AC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
}