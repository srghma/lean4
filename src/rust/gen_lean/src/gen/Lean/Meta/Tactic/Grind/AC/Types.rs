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
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_AC_instHashableExpr__lean: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_AC_instHashableSeq__lean: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17542774118954891045 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstr: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instInhabitedStruct: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instInhabitedState_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instInhabitedState: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_acExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(
    mut v_x_463_: *mut crate::leanh::LeanObject,
) -> u64 {
    if crate::leanh::lean_obj_tag(v_x_463_) == 0 {
        let mut v_x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_465_: u64 = 0;
        let mut v___x_466_: u64 = 0;
        let mut v___x_467_: u64 = 0;
        v_x_464_ = crate::leanh::lean_ctor_get(v_x_463_, 0);
        v___x_465_ = 0u64;
        v___x_466_ = lean_uint64_of_nat(v_x_464_);
        v___x_467_ = lean_uint64_mix_hash(v___x_465_, v___x_466_);
        return v___x_467_;
    } else {
        let mut v_lhs_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_470_: u64 = 0;
        let mut v___x_471_: u64 = 0;
        let mut v___x_472_: u64 = 0;
        let mut v___x_473_: u64 = 0;
        let mut v___x_474_: u64 = 0;
        v_lhs_468_ = crate::leanh::lean_ctor_get(v_x_463_, 0);
        v_rhs_469_ = crate::leanh::lean_ctor_get(v_x_463_, 1);
        v___x_470_ = 1u64;
        v___x_471_ = l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(v_lhs_468_);
        v___x_472_ = lean_uint64_mix_hash(v___x_470_, v___x_471_);
        v___x_473_ = l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(v_rhs_469_);
        v___x_474_ = lean_uint64_mix_hash(v___x_472_, v___x_473_);
        return v___x_474_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash___boxed(
    mut v_x_475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_476_: u64 = 0;
    let mut v_r_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_476_ = l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(v_x_475_);
    crate::leanh::lean_dec_ref(v_x_475_);
    v_r_477_ = crate::leanh::lean_box_uint64(v_res_476_);
    return v_r_477_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(
    mut v_x_480_: *mut crate::leanh::LeanObject,
) -> u64 {
    if crate::leanh::lean_obj_tag(v_x_480_) == 0 {
        let mut v_x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_482_: u64 = 0;
        let mut v___x_483_: u64 = 0;
        let mut v___x_484_: u64 = 0;
        v_x_481_ = crate::leanh::lean_ctor_get(v_x_480_, 0);
        v___x_482_ = 0u64;
        v___x_483_ = lean_uint64_of_nat(v_x_481_);
        v___x_484_ = lean_uint64_mix_hash(v___x_482_, v___x_483_);
        return v___x_484_;
    } else {
        let mut v_x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_s_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_487_: u64 = 0;
        let mut v___x_488_: u64 = 0;
        let mut v___x_489_: u64 = 0;
        let mut v___x_490_: u64 = 0;
        let mut v___x_491_: u64 = 0;
        v_x_485_ = crate::leanh::lean_ctor_get(v_x_480_, 0);
        v_s_486_ = crate::leanh::lean_ctor_get(v_x_480_, 1);
        v___x_487_ = 1u64;
        v___x_488_ = lean_uint64_of_nat(v_x_485_);
        v___x_489_ = lean_uint64_mix_hash(v___x_487_, v___x_488_);
        v___x_490_ = l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(v_s_486_);
        v___x_491_ = lean_uint64_mix_hash(v___x_489_, v___x_490_);
        return v___x_491_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash___boxed(
    mut v_x_492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_493_: u64 = 0;
    let mut v_r_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_493_ = l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(v_x_492_);
    crate::leanh::lean_dec_ref(v_x_492_);
    v_r_494_ = crate::leanh::lean_box_uint64(v_res_493_);
    return v_r_494_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx(
    mut v_x_497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_497_) {
        0 => {
            let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_498_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_498_;
        }
        1 => {
            let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_499_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_499_;
        }
        2 => {
            let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_500_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_500_;
        }
        3 => {
            let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_501_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_501_;
        }
        4 => {
            let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_502_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_502_;
        }
        5 => {
            let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_503_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_503_;
        }
        6 => {
            let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_504_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_504_;
        }
        7 => {
            let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_505_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_505_;
        }
        8 => {
            let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_506_ = crate::leanh::lean_unsigned_to_nat(8);
            return v___x_506_;
        }
        9 => {
            let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_507_ = crate::leanh::lean_unsigned_to_nat(9);
            return v___x_507_;
        }
        10 => {
            let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_508_ = crate::leanh::lean_unsigned_to_nat(10);
            return v___x_508_;
        }
        11 => {
            let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_509_ = crate::leanh::lean_unsigned_to_nat(11);
            return v___x_509_;
        }
        12 => {
            let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_510_ = crate::leanh::lean_unsigned_to_nat(12);
            return v___x_510_;
        }
        13 => {
            let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_511_ = crate::leanh::lean_unsigned_to_nat(13);
            return v___x_511_;
        }
        14 => {
            let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_512_ = crate::leanh::lean_unsigned_to_nat(14);
            return v___x_512_;
        }
        15 => {
            let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_513_ = crate::leanh::lean_unsigned_to_nat(15);
            return v___x_513_;
        }
        _ => {
            let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_514_ = crate::leanh::lean_unsigned_to_nat(16);
            return v___x_514_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx___boxed(
    mut v_x_515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_516_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx(v_x_515_);
    crate::leanh::lean_dec_ref(v_x_515_);
    return v_res_516_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
    mut v_t_517_: *mut crate::leanh::LeanObject,
    mut v_k_518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_517_) {
        0 => {
            let mut v_a_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ea_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_eb_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_519_ = crate::leanh::lean_ctor_get(v_t_517_, 0);
            crate::leanh::lean_inc_ref(v_a_519_);
            v_b_520_ = crate::leanh::lean_ctor_get(v_t_517_, 1);
            crate::leanh::lean_inc_ref(v_b_520_);
            v_ea_521_ = crate::leanh::lean_ctor_get(v_t_517_, 2);
            crate::leanh::lean_inc_ref(v_ea_521_);
            v_eb_522_ = crate::leanh::lean_ctor_get(v_t_517_, 3);
            crate::leanh::lean_inc_ref(v_eb_522_);
            crate::leanh::lean_dec_ref_known(v_t_517_, 4);
            v___x_523_ =
                crate::leanh::lean_apply_4(v_k_518_, v_a_519_, v_b_520_, v_ea_521_, v_eb_522_);
            return v___x_523_;
        }
        4 => {
            let mut v_lhs_524_: u8 = 0;
            let mut v_c_u2081_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_lhs_524_ = crate::leanh::lean_ctor_get_uint8(
                v_t_517_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
            );
            v_c_u2081_525_ = crate::leanh::lean_ctor_get(v_t_517_, 0);
            crate::leanh::lean_inc_ref(v_c_u2081_525_);
            v_c_u2082_526_ = crate::leanh::lean_ctor_get(v_t_517_, 1);
            crate::leanh::lean_inc_ref(v_c_u2082_526_);
            crate::leanh::lean_dec_ref_known(v_t_517_, 2);
            v___x_527_ = crate::leanh::lean_box((v_lhs_524_) as usize);
            v___x_528_ =
                crate::leanh::lean_apply_3(v_k_518_, v___x_527_, v_c_u2081_525_, v_c_u2082_526_);
            return v___x_528_;
        }
        5 => {
            let mut v_lhs_529_: u8 = 0;
            let mut v_s_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_lhs_529_ = crate::leanh::lean_ctor_get_uint8(
                v_t_517_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
            );
            v_s_530_ = crate::leanh::lean_ctor_get(v_t_517_, 0);
            crate::leanh::lean_inc_ref(v_s_530_);
            v_c_u2081_531_ = crate::leanh::lean_ctor_get(v_t_517_, 1);
            crate::leanh::lean_inc_ref(v_c_u2081_531_);
            v_c_u2082_532_ = crate::leanh::lean_ctor_get(v_t_517_, 2);
            crate::leanh::lean_inc_ref(v_c_u2082_532_);
            crate::leanh::lean_dec_ref_known(v_t_517_, 3);
            v___x_533_ = crate::leanh::lean_box((v_lhs_529_) as usize);
            v___x_534_ = crate::leanh::lean_apply_4(
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
            let mut v_s_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_lhs_535_ = crate::leanh::lean_ctor_get_uint8(
                v_t_517_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
            );
            v_s_536_ = crate::leanh::lean_ctor_get(v_t_517_, 0);
            crate::leanh::lean_inc_ref(v_s_536_);
            v_c_u2081_537_ = crate::leanh::lean_ctor_get(v_t_517_, 1);
            crate::leanh::lean_inc_ref(v_c_u2081_537_);
            v_c_u2082_538_ = crate::leanh::lean_ctor_get(v_t_517_, 2);
            crate::leanh::lean_inc_ref(v_c_u2082_538_);
            crate::leanh::lean_dec_ref_known(v_t_517_, 3);
            v___x_539_ = crate::leanh::lean_box((v_lhs_535_) as usize);
            v___x_540_ = crate::leanh::lean_apply_4(
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
            let mut v_s_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_lhs_541_ = crate::leanh::lean_ctor_get_uint8(
                v_t_517_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
            );
            v_s_542_ = crate::leanh::lean_ctor_get(v_t_517_, 0);
            crate::leanh::lean_inc_ref(v_s_542_);
            v_c_u2081_543_ = crate::leanh::lean_ctor_get(v_t_517_, 1);
            crate::leanh::lean_inc_ref(v_c_u2081_543_);
            v_c_u2082_544_ = crate::leanh::lean_ctor_get(v_t_517_, 2);
            crate::leanh::lean_inc_ref(v_c_u2082_544_);
            crate::leanh::lean_dec_ref_known(v_t_517_, 3);
            v___x_545_ = crate::leanh::lean_box((v_lhs_541_) as usize);
            v___x_546_ = crate::leanh::lean_apply_4(
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
            let mut v_s_u2081_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_u2082_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_lhs_547_ = crate::leanh::lean_ctor_get_uint8(
                v_t_517_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
            );
            v_s_u2081_548_ = crate::leanh::lean_ctor_get(v_t_517_, 0);
            crate::leanh::lean_inc_ref(v_s_u2081_548_);
            v_s_u2082_549_ = crate::leanh::lean_ctor_get(v_t_517_, 1);
            crate::leanh::lean_inc_ref(v_s_u2082_549_);
            v_c_u2081_550_ = crate::leanh::lean_ctor_get(v_t_517_, 2);
            crate::leanh::lean_inc_ref(v_c_u2081_550_);
            v_c_u2082_551_ = crate::leanh::lean_ctor_get(v_t_517_, 3);
            crate::leanh::lean_inc_ref(v_c_u2082_551_);
            crate::leanh::lean_dec_ref_known(v_t_517_, 4);
            v___x_552_ = crate::leanh::lean_box((v_lhs_547_) as usize);
            v___x_553_ = crate::leanh::lean_apply_5(
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
            let mut v_r_u2081_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_u2082_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_r_u2081_554_ = crate::leanh::lean_ctor_get(v_t_517_, 0);
            crate::leanh::lean_inc_ref(v_r_u2081_554_);
            v_c_555_ = crate::leanh::lean_ctor_get(v_t_517_, 1);
            crate::leanh::lean_inc_ref(v_c_555_);
            v_r_u2082_556_ = crate::leanh::lean_ctor_get(v_t_517_, 2);
            crate::leanh::lean_inc_ref(v_r_u2082_556_);
            v_c_u2081_557_ = crate::leanh::lean_ctor_get(v_t_517_, 3);
            crate::leanh::lean_inc_ref(v_c_u2081_557_);
            v_c_u2082_558_ = crate::leanh::lean_ctor_get(v_t_517_, 4);
            crate::leanh::lean_inc_ref(v_c_u2082_558_);
            crate::leanh::lean_dec_ref_known(v_t_517_, 5);
            v___x_559_ = crate::leanh::lean_apply_5(
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
            let mut v_p_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_p_560_ = crate::leanh::lean_ctor_get(v_t_517_, 0);
            crate::leanh::lean_inc_ref(v_p_560_);
            v_s_561_ = crate::leanh::lean_ctor_get(v_t_517_, 1);
            crate::leanh::lean_inc_ref(v_s_561_);
            v_c_562_ = crate::leanh::lean_ctor_get(v_t_517_, 2);
            crate::leanh::lean_inc_ref(v_c_562_);
            v_c_u2081_563_ = crate::leanh::lean_ctor_get(v_t_517_, 3);
            crate::leanh::lean_inc_ref(v_c_u2081_563_);
            v_c_u2082_564_ = crate::leanh::lean_ctor_get(v_t_517_, 4);
            crate::leanh::lean_inc_ref(v_c_u2082_564_);
            crate::leanh::lean_dec_ref_known(v_t_517_, 5);
            v___x_565_ = crate::leanh::lean_apply_5(
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
            let mut v_x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_566_ = crate::leanh::lean_ctor_get(v_t_517_, 0);
            crate::leanh::lean_inc(v_x_566_);
            v_c_u2081_567_ = crate::leanh::lean_ctor_get(v_t_517_, 1);
            crate::leanh::lean_inc_ref(v_c_u2081_567_);
            crate::leanh::lean_dec_ref_known(v_t_517_, 2);
            v___x_568_ = crate::leanh::lean_apply_2(v_k_518_, v_x_566_, v_c_u2081_567_);
            return v___x_568_;
        }
        12 => {
            let mut v_x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_569_ = crate::leanh::lean_ctor_get(v_t_517_, 0);
            crate::leanh::lean_inc(v_x_569_);
            v_c_u2081_570_ = crate::leanh::lean_ctor_get(v_t_517_, 1);
            crate::leanh::lean_inc_ref(v_c_u2081_570_);
            crate::leanh::lean_dec_ref_known(v_t_517_, 2);
            v___x_571_ = crate::leanh::lean_apply_2(v_k_518_, v_x_569_, v_c_u2081_570_);
            return v___x_571_;
        }
        13 => {
            let mut v_x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_572_ = crate::leanh::lean_ctor_get(v_t_517_, 0);
            crate::leanh::lean_inc(v_x_572_);
            v_c_u2081_573_ = crate::leanh::lean_ctor_get(v_t_517_, 1);
            crate::leanh::lean_inc_ref(v_c_u2081_573_);
            crate::leanh::lean_dec_ref_known(v_t_517_, 2);
            v___x_574_ = crate::leanh::lean_apply_2(v_k_518_, v_x_572_, v_c_u2081_573_);
            return v___x_574_;
        }
        _ => {
            let mut v_c_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_575_ = crate::leanh::lean_ctor_get(v_t_517_, 0);
            crate::leanh::lean_inc_ref(v_c_575_);
            crate::leanh::lean_dec_ref(v_t_517_);
            v___x_576_ = crate::leanh::lean_apply_1(v_k_518_, v_c_575_);
            return v___x_576_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim(
    mut v_motive__2_577_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_578_: *mut crate::leanh::LeanObject,
    mut v_t_579_: *mut crate::leanh::LeanObject,
    mut v_h_580_: *mut crate::leanh::LeanObject,
    mut v_k_581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_582_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_579_, v_k_581_);
    return v___x_582_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___boxed(
    mut v_motive__2_583_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_584_: *mut crate::leanh::LeanObject,
    mut v_t_585_: *mut crate::leanh::LeanObject,
    mut v_h_586_: *mut crate::leanh::LeanObject,
    mut v_k_587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_588_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim(
        v_motive__2_583_,
        v_ctorIdx_584_,
        v_t_585_,
        v_h_586_,
        v_k_587_,
    );
    crate::leanh::lean_dec(v_ctorIdx_584_);
    return v_res_588_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_core_elim___redArg(
    mut v_t_589_: *mut crate::leanh::LeanObject,
    mut v_core_590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_591_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_589_, v_core_590_);
    return v___x_591_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_core_elim(
    mut v_motive__2_592_: *mut crate::leanh::LeanObject,
    mut v_t_593_: *mut crate::leanh::LeanObject,
    mut v_h_594_: *mut crate::leanh::LeanObject,
    mut v_core_595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_596_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_593_, v_core_595_);
    return v___x_596_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup_elim___redArg(
    mut v_t_597_: *mut crate::leanh::LeanObject,
    mut v_erase__dup_598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_599_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_597_, v_erase__dup_598_);
    return v___x_599_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup_elim(
    mut v_motive__2_600_: *mut crate::leanh::LeanObject,
    mut v_t_601_: *mut crate::leanh::LeanObject,
    mut v_h_602_: *mut crate::leanh::LeanObject,
    mut v_erase__dup_603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_604_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_601_, v_erase__dup_603_);
    return v___x_604_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase0_elim___redArg(
    mut v_t_605_: *mut crate::leanh::LeanObject,
    mut v_erase0_606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_607_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_605_, v_erase0_606_);
    return v___x_607_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase0_elim(
    mut v_motive__2_608_: *mut crate::leanh::LeanObject,
    mut v_t_609_: *mut crate::leanh::LeanObject,
    mut v_h_610_: *mut crate::leanh::LeanObject,
    mut v_erase0_611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_612_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_609_, v_erase0_611_);
    return v___x_612_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_swap_elim___redArg(
    mut v_t_613_: *mut crate::leanh::LeanObject,
    mut v_swap_614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_615_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_613_, v_swap_614_);
    return v___x_615_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_swap_elim(
    mut v_motive__2_616_: *mut crate::leanh::LeanObject,
    mut v_t_617_: *mut crate::leanh::LeanObject,
    mut v_h_618_: *mut crate::leanh::LeanObject,
    mut v_swap_619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_620_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_617_, v_swap_619_);
    return v___x_620_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__exact_elim___redArg(
    mut v_t_621_: *mut crate::leanh::LeanObject,
    mut v_simp__exact_622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_623_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_621_, v_simp__exact_622_);
    return v___x_623_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__exact_elim(
    mut v_motive__2_624_: *mut crate::leanh::LeanObject,
    mut v_t_625_: *mut crate::leanh::LeanObject,
    mut v_h_626_: *mut crate::leanh::LeanObject,
    mut v_simp__exact_627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_628_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_625_, v_simp__exact_627_);
    return v___x_628_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__ac_elim___redArg(
    mut v_t_629_: *mut crate::leanh::LeanObject,
    mut v_simp__ac_630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_631_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_629_, v_simp__ac_630_);
    return v___x_631_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__ac_elim(
    mut v_motive__2_632_: *mut crate::leanh::LeanObject,
    mut v_t_633_: *mut crate::leanh::LeanObject,
    mut v_h_634_: *mut crate::leanh::LeanObject,
    mut v_simp__ac_635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_636_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_633_, v_simp__ac_635_);
    return v___x_636_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__suffix_elim___redArg(
    mut v_t_637_: *mut crate::leanh::LeanObject,
    mut v_simp__suffix_638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_639_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_637_, v_simp__suffix_638_);
    return v___x_639_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__suffix_elim(
    mut v_motive__2_640_: *mut crate::leanh::LeanObject,
    mut v_t_641_: *mut crate::leanh::LeanObject,
    mut v_h_642_: *mut crate::leanh::LeanObject,
    mut v_simp__suffix_643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_644_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_641_, v_simp__suffix_643_);
    return v___x_644_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__prefix_elim___redArg(
    mut v_t_645_: *mut crate::leanh::LeanObject,
    mut v_simp__prefix_646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_647_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_645_, v_simp__prefix_646_);
    return v___x_647_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__prefix_elim(
    mut v_motive__2_648_: *mut crate::leanh::LeanObject,
    mut v_t_649_: *mut crate::leanh::LeanObject,
    mut v_h_650_: *mut crate::leanh::LeanObject,
    mut v_simp__prefix_651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_652_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_649_, v_simp__prefix_651_);
    return v___x_652_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__middle_elim___redArg(
    mut v_t_653_: *mut crate::leanh::LeanObject,
    mut v_simp__middle_654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_655_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_653_, v_simp__middle_654_);
    return v___x_655_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__middle_elim(
    mut v_motive__2_656_: *mut crate::leanh::LeanObject,
    mut v_t_657_: *mut crate::leanh::LeanObject,
    mut v_h_658_: *mut crate::leanh::LeanObject,
    mut v_simp__middle_659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_660_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_657_, v_simp__middle_659_);
    return v___x_660_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac_elim___redArg(
    mut v_t_661_: *mut crate::leanh::LeanObject,
    mut v_superpose__ac_662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_663_ =
        l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_661_, v_superpose__ac_662_);
    return v___x_663_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac_elim(
    mut v_motive__2_664_: *mut crate::leanh::LeanObject,
    mut v_t_665_: *mut crate::leanh::LeanObject,
    mut v_h_666_: *mut crate::leanh::LeanObject,
    mut v_superpose__ac_667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_668_ =
        l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_665_, v_superpose__ac_667_);
    return v___x_668_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose_elim___redArg(
    mut v_t_669_: *mut crate::leanh::LeanObject,
    mut v_superpose_670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_671_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_669_, v_superpose_670_);
    return v___x_671_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose_elim(
    mut v_motive__2_672_: *mut crate::leanh::LeanObject,
    mut v_t_673_: *mut crate::leanh::LeanObject,
    mut v_h_674_: *mut crate::leanh::LeanObject,
    mut v_superpose_675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_676_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_673_, v_superpose_675_);
    return v___x_676_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac__idempotent_elim___redArg(
    mut v_t_677_: *mut crate::leanh::LeanObject,
    mut v_superpose__ac__idempotent_678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_679_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
        v_t_677_,
        v_superpose__ac__idempotent_678_,
    );
    return v___x_679_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac__idempotent_elim(
    mut v_motive__2_680_: *mut crate::leanh::LeanObject,
    mut v_t_681_: *mut crate::leanh::LeanObject,
    mut v_h_682_: *mut crate::leanh::LeanObject,
    mut v_superpose__ac__idempotent_683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_684_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
        v_t_681_,
        v_superpose__ac__idempotent_683_,
    );
    return v___x_684_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__head__idempotent_elim___redArg(
    mut v_t_685_: *mut crate::leanh::LeanObject,
    mut v_superpose__head__idempotent_686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_687_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
        v_t_685_,
        v_superpose__head__idempotent_686_,
    );
    return v___x_687_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__head__idempotent_elim(
    mut v_motive__2_688_: *mut crate::leanh::LeanObject,
    mut v_t_689_: *mut crate::leanh::LeanObject,
    mut v_h_690_: *mut crate::leanh::LeanObject,
    mut v_superpose__head__idempotent_691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_692_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
        v_t_689_,
        v_superpose__head__idempotent_691_,
    );
    return v___x_692_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__tail__idempotent_elim___redArg(
    mut v_t_693_: *mut crate::leanh::LeanObject,
    mut v_superpose__tail__idempotent_694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_695_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
        v_t_693_,
        v_superpose__tail__idempotent_694_,
    );
    return v___x_695_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__tail__idempotent_elim(
    mut v_motive__2_696_: *mut crate::leanh::LeanObject,
    mut v_t_697_: *mut crate::leanh::LeanObject,
    mut v_h_698_: *mut crate::leanh::LeanObject,
    mut v_superpose__tail__idempotent_699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_700_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
        v_t_697_,
        v_superpose__tail__idempotent_699_,
    );
    return v___x_700_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_refl_elim___redArg(
    mut v_t_701_: *mut crate::leanh::LeanObject,
    mut v_refl_702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_703_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_701_, v_refl_702_);
    return v___x_703_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_refl_elim(
    mut v_motive__2_704_: *mut crate::leanh::LeanObject,
    mut v_t_705_: *mut crate::leanh::LeanObject,
    mut v_h_706_: *mut crate::leanh::LeanObject,
    mut v_refl_707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_708_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_705_, v_refl_707_);
    return v___x_708_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup__rhs_elim___redArg(
    mut v_t_709_: *mut crate::leanh::LeanObject,
    mut v_erase__dup__rhs_710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_711_ =
        l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_709_, v_erase__dup__rhs_710_);
    return v___x_711_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup__rhs_elim(
    mut v_motive__2_712_: *mut crate::leanh::LeanObject,
    mut v_t_713_: *mut crate::leanh::LeanObject,
    mut v_h_714_: *mut crate::leanh::LeanObject,
    mut v_erase__dup__rhs_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_716_ =
        l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_713_, v_erase__dup__rhs_715_);
    return v___x_716_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase0__rhs_elim___redArg(
    mut v_t_717_: *mut crate::leanh::LeanObject,
    mut v_erase0__rhs_718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_719_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_717_, v_erase0__rhs_718_);
    return v___x_719_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase0__rhs_elim(
    mut v_motive__2_720_: *mut crate::leanh::LeanObject,
    mut v_t_721_: *mut crate::leanh::LeanObject,
    mut v_h_722_: *mut crate::leanh::LeanObject,
    mut v_erase0__rhs_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_724_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_721_, v_erase0__rhs_723_);
    return v___x_724_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_728_ = crate::leanh::lean_box(0);
    v___x_729_ = l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1;
    v___x_730_ = l_Lean_Expr_const___override(v___x_729_, v___x_728_);
    return v___x_730_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_731_ = l_Lean_Grind_AC_instInhabitedExpr_default;
    v___x_732_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2,
    );
    v___x_733_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_733_, 0, v___x_732_);
    crate::leanh::lean_ctor_set(v___x_733_, 1, v___x_732_);
    crate::leanh::lean_ctor_set(v___x_733_, 2, v___x_731_);
    crate::leanh::lean_ctor_set(v___x_733_, 3, v___x_731_);
    return v___x_733_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof() -> *mut crate::leanh::LeanObject
{
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_734_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3,
    );
    return v___x_734_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_735_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_736_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3,
    );
    v___x_737_ = l_Lean_Grind_AC_instInhabitedSeq_default;
    v___x_738_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_738_, 0, v___x_737_);
    crate::leanh::lean_ctor_set(v___x_738_, 1, v___x_737_);
    crate::leanh::lean_ctor_set(v___x_738_, 2, v___x_736_);
    crate::leanh::lean_ctor_set(v___x_738_, 3, v___x_735_);
    return v___x_738_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr() -> *mut crate::leanh::LeanObject {
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_739_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0,
    );
    return v___x_739_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_compare(
    mut v_c_u2081_740_: *mut crate::leanh::LeanObject,
    mut v_c_u2082_741_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lhs_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: u8 = 0;
    v_lhs_742_ = crate::leanh::lean_ctor_get(v_c_u2081_740_, 0);
    v_id_743_ = crate::leanh::lean_ctor_get(v_c_u2081_740_, 3);
    v_lhs_744_ = crate::leanh::lean_ctor_get(v_c_u2082_741_, 0);
    v_id_745_ = crate::leanh::lean_ctor_get(v_c_u2082_741_, 3);
    v___x_746_ = l_Lean_Grind_AC_Seq_length(v_lhs_742_);
    v___x_747_ = l_Lean_Grind_AC_Seq_length(v_lhs_744_);
    v___x_748_ = lean_nat_dec_lt(v___x_746_, v___x_747_);
    if v___x_748_ == 0 {
        let mut v___x_749_: u8 = 0;
        v___x_749_ = lean_nat_dec_eq(v___x_746_, v___x_747_);
        crate::leanh::lean_dec(v___x_747_);
        crate::leanh::lean_dec(v___x_746_);
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
        crate::leanh::lean_dec(v___x_747_);
        crate::leanh::lean_dec(v___x_746_);
        v___x_756_ = 0;
        return v___x_756_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_compare___boxed(
    mut v_c_u2081_757_: *mut crate::leanh::LeanObject,
    mut v_c_u2082_758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_759_: u8 = 0;
    let mut v_r_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_759_ = l_Lean_Meta_Grind_AC_EqCnstr_compare(v_c_u2081_757_, v_c_u2082_758_);
    crate::leanh::lean_dec_ref(v_c_u2082_758_);
    crate::leanh::lean_dec_ref(v_c_u2081_757_);
    v_r_760_ = crate::leanh::lean_box((v_res_759_) as usize);
    return v_r_760_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx(
    mut v_x_761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_761_) {
        0 => {
            let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_762_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_762_;
        }
        1 => {
            let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_763_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_763_;
        }
        2 => {
            let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_764_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_764_;
        }
        3 => {
            let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_765_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_765_;
        }
        4 => {
            let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_766_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_766_;
        }
        5 => {
            let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_767_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_767_;
        }
        6 => {
            let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_768_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_768_;
        }
        _ => {
            let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_769_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_769_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx___boxed(
    mut v_x_770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_771_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx(v_x_770_);
    crate::leanh::lean_dec_ref(v_x_770_);
    return v_res_771_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(
    mut v_t_772_: *mut crate::leanh::LeanObject,
    mut v_k_773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_772_) {
        0 => {
            let mut v_a_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ea_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_eb_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_774_ = crate::leanh::lean_ctor_get(v_t_772_, 0);
            crate::leanh::lean_inc_ref(v_a_774_);
            v_b_775_ = crate::leanh::lean_ctor_get(v_t_772_, 1);
            crate::leanh::lean_inc_ref(v_b_775_);
            v_ea_776_ = crate::leanh::lean_ctor_get(v_t_772_, 2);
            crate::leanh::lean_inc_ref(v_ea_776_);
            v_eb_777_ = crate::leanh::lean_ctor_get(v_t_772_, 3);
            crate::leanh::lean_inc_ref(v_eb_777_);
            crate::leanh::lean_dec_ref_known(v_t_772_, 4);
            v___x_778_ =
                crate::leanh::lean_apply_4(v_k_773_, v_a_774_, v_b_775_, v_ea_776_, v_eb_777_);
            return v___x_778_;
        }
        1 => {
            let mut v_c_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_779_ = crate::leanh::lean_ctor_get(v_t_772_, 0);
            crate::leanh::lean_inc_ref(v_c_779_);
            crate::leanh::lean_dec_ref_known(v_t_772_, 1);
            v___x_780_ = crate::leanh::lean_apply_1(v_k_773_, v_c_779_);
            return v___x_780_;
        }
        2 => {
            let mut v_c_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_781_ = crate::leanh::lean_ctor_get(v_t_772_, 0);
            crate::leanh::lean_inc_ref(v_c_781_);
            crate::leanh::lean_dec_ref_known(v_t_772_, 1);
            v___x_782_ = crate::leanh::lean_apply_1(v_k_773_, v_c_781_);
            return v___x_782_;
        }
        3 => {
            let mut v_lhs_783_: u8 = 0;
            let mut v_c_u2081_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_lhs_783_ = crate::leanh::lean_ctor_get_uint8(
                v_t_772_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
            );
            v_c_u2081_784_ = crate::leanh::lean_ctor_get(v_t_772_, 0);
            crate::leanh::lean_inc_ref(v_c_u2081_784_);
            v_c_u2082_785_ = crate::leanh::lean_ctor_get(v_t_772_, 1);
            crate::leanh::lean_inc_ref(v_c_u2082_785_);
            crate::leanh::lean_dec_ref_known(v_t_772_, 2);
            v___x_786_ = crate::leanh::lean_box((v_lhs_783_) as usize);
            v___x_787_ =
                crate::leanh::lean_apply_3(v_k_773_, v___x_786_, v_c_u2081_784_, v_c_u2082_785_);
            return v___x_787_;
        }
        7 => {
            let mut v_lhs_788_: u8 = 0;
            let mut v_s_u2081_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_u2082_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_lhs_788_ = crate::leanh::lean_ctor_get_uint8(
                v_t_772_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
            );
            v_s_u2081_789_ = crate::leanh::lean_ctor_get(v_t_772_, 0);
            crate::leanh::lean_inc_ref(v_s_u2081_789_);
            v_s_u2082_790_ = crate::leanh::lean_ctor_get(v_t_772_, 1);
            crate::leanh::lean_inc_ref(v_s_u2082_790_);
            v_c_u2081_791_ = crate::leanh::lean_ctor_get(v_t_772_, 2);
            crate::leanh::lean_inc_ref(v_c_u2081_791_);
            v_c_u2082_792_ = crate::leanh::lean_ctor_get(v_t_772_, 3);
            crate::leanh::lean_inc_ref(v_c_u2082_792_);
            crate::leanh::lean_dec_ref_known(v_t_772_, 4);
            v___x_793_ = crate::leanh::lean_box((v_lhs_788_) as usize);
            v___x_794_ = crate::leanh::lean_apply_5(
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
            let mut v_s_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_lhs_795_ = crate::leanh::lean_ctor_get_uint8(
                v_t_772_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
            );
            v_s_796_ = crate::leanh::lean_ctor_get(v_t_772_, 0);
            crate::leanh::lean_inc_ref(v_s_796_);
            v_c_u2081_797_ = crate::leanh::lean_ctor_get(v_t_772_, 1);
            crate::leanh::lean_inc_ref(v_c_u2081_797_);
            v_c_u2082_798_ = crate::leanh::lean_ctor_get(v_t_772_, 2);
            crate::leanh::lean_inc_ref(v_c_u2082_798_);
            crate::leanh::lean_dec_ref(v_t_772_);
            v___x_799_ = crate::leanh::lean_box((v_lhs_795_) as usize);
            v___x_800_ = crate::leanh::lean_apply_4(
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
    mut v_motive__2_801_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_802_: *mut crate::leanh::LeanObject,
    mut v_t_803_: *mut crate::leanh::LeanObject,
    mut v_h_804_: *mut crate::leanh::LeanObject,
    mut v_k_805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_806_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_803_, v_k_805_);
    return v___x_806_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___boxed(
    mut v_motive__2_807_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_808_: *mut crate::leanh::LeanObject,
    mut v_t_809_: *mut crate::leanh::LeanObject,
    mut v_h_810_: *mut crate::leanh::LeanObject,
    mut v_k_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_812_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim(
        v_motive__2_807_,
        v_ctorIdx_808_,
        v_t_809_,
        v_h_810_,
        v_k_811_,
    );
    crate::leanh::lean_dec(v_ctorIdx_808_);
    return v_res_812_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_core_elim___redArg(
    mut v_t_813_: *mut crate::leanh::LeanObject,
    mut v_core_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_815_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_813_, v_core_814_);
    return v___x_815_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_core_elim(
    mut v_motive__2_816_: *mut crate::leanh::LeanObject,
    mut v_t_817_: *mut crate::leanh::LeanObject,
    mut v_h_818_: *mut crate::leanh::LeanObject,
    mut v_core_819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_820_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_817_, v_core_819_);
    return v___x_820_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase__dup_elim___redArg(
    mut v_t_821_: *mut crate::leanh::LeanObject,
    mut v_erase__dup_822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_823_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_821_, v_erase__dup_822_);
    return v___x_823_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase__dup_elim(
    mut v_motive__2_824_: *mut crate::leanh::LeanObject,
    mut v_t_825_: *mut crate::leanh::LeanObject,
    mut v_h_826_: *mut crate::leanh::LeanObject,
    mut v_erase__dup_827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_828_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_825_, v_erase__dup_827_);
    return v___x_828_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase0_elim___redArg(
    mut v_t_829_: *mut crate::leanh::LeanObject,
    mut v_erase0_830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_829_, v_erase0_830_);
    return v___x_831_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase0_elim(
    mut v_motive__2_832_: *mut crate::leanh::LeanObject,
    mut v_t_833_: *mut crate::leanh::LeanObject,
    mut v_h_834_: *mut crate::leanh::LeanObject,
    mut v_erase0_835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_836_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_833_, v_erase0_835_);
    return v___x_836_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__exact_elim___redArg(
    mut v_t_837_: *mut crate::leanh::LeanObject,
    mut v_simp__exact_838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_839_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_837_, v_simp__exact_838_);
    return v___x_839_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__exact_elim(
    mut v_motive__2_840_: *mut crate::leanh::LeanObject,
    mut v_t_841_: *mut crate::leanh::LeanObject,
    mut v_h_842_: *mut crate::leanh::LeanObject,
    mut v_simp__exact_843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_844_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_841_, v_simp__exact_843_);
    return v___x_844_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__ac_elim___redArg(
    mut v_t_845_: *mut crate::leanh::LeanObject,
    mut v_simp__ac_846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_847_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_845_, v_simp__ac_846_);
    return v___x_847_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__ac_elim(
    mut v_motive__2_848_: *mut crate::leanh::LeanObject,
    mut v_t_849_: *mut crate::leanh::LeanObject,
    mut v_h_850_: *mut crate::leanh::LeanObject,
    mut v_simp__ac_851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_852_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_849_, v_simp__ac_851_);
    return v___x_852_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__suffix_elim___redArg(
    mut v_t_853_: *mut crate::leanh::LeanObject,
    mut v_simp__suffix_854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_855_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_853_, v_simp__suffix_854_);
    return v___x_855_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__suffix_elim(
    mut v_motive__2_856_: *mut crate::leanh::LeanObject,
    mut v_t_857_: *mut crate::leanh::LeanObject,
    mut v_h_858_: *mut crate::leanh::LeanObject,
    mut v_simp__suffix_859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_860_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_857_, v_simp__suffix_859_);
    return v___x_860_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__prefix_elim___redArg(
    mut v_t_861_: *mut crate::leanh::LeanObject,
    mut v_simp__prefix_862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_863_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_861_, v_simp__prefix_862_);
    return v___x_863_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__prefix_elim(
    mut v_motive__2_864_: *mut crate::leanh::LeanObject,
    mut v_t_865_: *mut crate::leanh::LeanObject,
    mut v_h_866_: *mut crate::leanh::LeanObject,
    mut v_simp__prefix_867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_868_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_865_, v_simp__prefix_867_);
    return v___x_868_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__middle_elim___redArg(
    mut v_t_869_: *mut crate::leanh::LeanObject,
    mut v_simp__middle_870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_871_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_869_, v_simp__middle_870_);
    return v___x_871_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__middle_elim(
    mut v_motive__2_872_: *mut crate::leanh::LeanObject,
    mut v_t_873_: *mut crate::leanh::LeanObject,
    mut v_h_874_: *mut crate::leanh::LeanObject,
    mut v_simp__middle_875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_876_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_873_, v_simp__middle_875_);
    return v___x_876_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_877_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_878_ = lean_mk_empty_array_with_capacity(v___x_877_);
    v___x_879_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_879_, 0, v___x_878_);
    return v___x_879_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_880_: usize = 0;
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_880_ = 5usize;
    v___x_881_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_882_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_883_ = lean_mk_empty_array_with_capacity(v___x_882_);
    v___x_884_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0,
    );
    v___x_885_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_885_, 0, v___x_884_);
    crate::leanh::lean_ctor_set(v___x_885_, 1, v___x_883_);
    crate::leanh::lean_ctor_set(v___x_885_, 2, v___x_881_);
    crate::leanh::lean_ctor_set(v___x_885_, 3, v___x_881_);
    crate::leanh::lean_ctor_set_usize(v___x_885_, 4, v___x_880_);
    return v___x_885_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_886_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_886_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_887_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2,
    );
    v___x_888_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_888_, 0, v___x_887_);
    return v___x_888_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_889_: u8 = 0;
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_889_ = 0;
    v___x_890_ = crate::leanh::lean_box(0);
    v___x_891_ = crate::leanh::lean_box(1);
    v___x_892_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3,
    );
    v___x_893_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1,
    );
    v___x_894_ = crate::leanh::lean_box(0);
    v___x_895_ = crate::leanh::lean_box(0);
    v___x_896_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2,
    );
    v___x_897_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_898_ = crate::leanh::lean_alloc_ctor(0, 17, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_898_, 0, v___x_897_);
    crate::leanh::lean_ctor_set(v___x_898_, 1, v___x_896_);
    crate::leanh::lean_ctor_set(v___x_898_, 2, v___x_895_);
    crate::leanh::lean_ctor_set(v___x_898_, 3, v___x_896_);
    crate::leanh::lean_ctor_set(v___x_898_, 4, v___x_894_);
    crate::leanh::lean_ctor_set(v___x_898_, 5, v___x_896_);
    crate::leanh::lean_ctor_set(v___x_898_, 6, v___x_894_);
    crate::leanh::lean_ctor_set(v___x_898_, 7, v___x_894_);
    crate::leanh::lean_ctor_set(v___x_898_, 8, v___x_894_);
    crate::leanh::lean_ctor_set(v___x_898_, 9, v___x_897_);
    crate::leanh::lean_ctor_set(v___x_898_, 10, v___x_893_);
    crate::leanh::lean_ctor_set(v___x_898_, 11, v___x_892_);
    crate::leanh::lean_ctor_set(v___x_898_, 12, v___x_892_);
    crate::leanh::lean_ctor_set(v___x_898_, 13, v___x_893_);
    crate::leanh::lean_ctor_set(v___x_898_, 14, v___x_891_);
    crate::leanh::lean_ctor_set(v___x_898_, 15, v___x_890_);
    crate::leanh::lean_ctor_set(v___x_898_, 16, v___x_893_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_898_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
        v___x_889_,
    );
    return v___x_898_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_899_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4,
    );
    return v___x_899_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct() -> *mut crate::leanh::LeanObject {
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_900_ = l_Lean_Meta_Grind_AC_instInhabitedStruct_default;
    return v___x_900_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_903_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_903_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_904_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1,
    );
    v___x_905_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_905_, 0, v___x_904_);
    return v___x_905_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_906_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_907_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2,
    );
    v___x_908_ = l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__0;
    v___x_909_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_909_, 0, v___x_908_);
    crate::leanh::lean_ctor_set(v___x_909_, 1, v___x_907_);
    crate::leanh::lean_ctor_set(v___x_909_, 2, v___x_907_);
    crate::leanh::lean_ctor_set(v___x_909_, 3, v___x_906_);
    return v___x_909_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedState_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_910_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3,
    );
    return v___x_910_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedState() -> *mut crate::leanh::LeanObject {
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_911_ = l_Lean_Meta_Grind_AC_instInhabitedState_default;
    return v___x_911_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(
    mut v___x_912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_914_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_914_, 0, v___x_912_);
    return v___x_914_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed(
    mut v___x_915_: *mut crate::leanh::LeanObject,
    mut v___y_916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_917_ = l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(v___x_915_);
    return v_res_917_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_918_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3,
    );
    v___f_919_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_919_, 0, v___x_918_);
    return v___f_919_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_921_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_);
    v___x_922_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_921_);
    return v___x_922_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed(
    mut v_a_923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_924_ = l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_();
    return v_res_924_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_AC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof =
        _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof);
    l_Lean_Meta_Grind_AC_instInhabitedEqCnstr = _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedEqCnstr);
    l_Lean_Meta_Grind_AC_instInhabitedStruct_default =
        _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedStruct_default);
    l_Lean_Meta_Grind_AC_instInhabitedStruct = _init_l_Lean_Meta_Grind_AC_instInhabitedStruct();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedStruct);
    l_Lean_Meta_Grind_AC_instInhabitedState_default =
        _init_l_Lean_Meta_Grind_AC_instInhabitedState_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedState_default);
    l_Lean_Meta_Grind_AC_instInhabitedState = _init_l_Lean_Meta_Grind_AC_instInhabitedState();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedState);
    res = l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Grind_AC_acExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_AC_acExt);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_AC_Types(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_AC_Types(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_AC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
}
