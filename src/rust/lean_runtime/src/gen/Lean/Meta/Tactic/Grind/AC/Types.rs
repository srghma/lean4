// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.Types
// Imports: Init.Grind.AC Std.Data.HashMap Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.AC.Seq
use crate::r#gen::Init::Grind::AC::{
    initialize_Init_Grind_AC, l_Lean_Grind_AC_instInhabitedExpr_default,
    l_Lean_Grind_AC_instInhabitedSeq_default, runtime_initialize_Init_Grind_AC,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
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
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint64_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_lt, lean_uint64_mix_hash,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_5, lean_box, lean_box_uint64,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_AC_instHashableExpr__lean: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_AC_instHashableSeq__lean: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0_value: LeanStringObject<20> =
    LeanStringObject {
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
            95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109,
            121, 0,
        ],
    };
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0_value)
                as *mut LeanObject,
            17542774118954891045 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instInhabitedEqCnstr: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instInhabitedStruct_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instInhabitedStruct: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instInhabitedState_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instInhabitedState: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(
    mut v_x_463_: *mut LeanObject,
) -> u64 {
    if lean_obj_tag(v_x_463_) == 0 {
        let mut v_x_464_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_465_: u64 = 0;
        let mut v___x_466_: u64 = 0;
        let mut v___x_467_: u64 = 0;
        v_x_464_ = lean_ctor_get(v_x_463_, 0);
        v___x_465_ = 0u64;
        v___x_466_ = lean_uint64_of_nat(v_x_464_);
        v___x_467_ = lean_uint64_mix_hash(v___x_465_, v___x_466_);
        return v___x_467_;
    } else {
        let mut v_lhs_468_: *mut LeanObject = core::ptr::null_mut();
        let mut v_rhs_469_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_470_: u64 = 0;
        let mut v___x_471_: u64 = 0;
        let mut v___x_472_: u64 = 0;
        let mut v___x_473_: u64 = 0;
        let mut v___x_474_: u64 = 0;
        v_lhs_468_ = lean_ctor_get(v_x_463_, 0);
        v_rhs_469_ = lean_ctor_get(v_x_463_, 1);
        v___x_470_ = 1u64;
        v___x_471_ = l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(v_lhs_468_);
        v___x_472_ = lean_uint64_mix_hash(v___x_470_, v___x_471_);
        v___x_473_ = l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(v_rhs_469_);
        v___x_474_ = lean_uint64_mix_hash(v___x_472_, v___x_473_);
        return v___x_474_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash___boxed(
    mut v_x_475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_476_: u64 = 0;
    let mut v_r_477_: *mut LeanObject = core::ptr::null_mut();
    v_res_476_ = l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(v_x_475_);
    lean_dec_ref(v_x_475_);
    v_r_477_ = lean_box_uint64(v_res_476_);
    return v_r_477_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(
    mut v_x_480_: *mut LeanObject,
) -> u64 {
    if lean_obj_tag(v_x_480_) == 0 {
        let mut v_x_481_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_482_: u64 = 0;
        let mut v___x_483_: u64 = 0;
        let mut v___x_484_: u64 = 0;
        v_x_481_ = lean_ctor_get(v_x_480_, 0);
        v___x_482_ = 0u64;
        v___x_483_ = lean_uint64_of_nat(v_x_481_);
        v___x_484_ = lean_uint64_mix_hash(v___x_482_, v___x_483_);
        return v___x_484_;
    } else {
        let mut v_x_485_: *mut LeanObject = core::ptr::null_mut();
        let mut v_s_486_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_487_: u64 = 0;
        let mut v___x_488_: u64 = 0;
        let mut v___x_489_: u64 = 0;
        let mut v___x_490_: u64 = 0;
        let mut v___x_491_: u64 = 0;
        v_x_485_ = lean_ctor_get(v_x_480_, 0);
        v_s_486_ = lean_ctor_get(v_x_480_, 1);
        v___x_487_ = 1u64;
        v___x_488_ = lean_uint64_of_nat(v_x_485_);
        v___x_489_ = lean_uint64_mix_hash(v___x_487_, v___x_488_);
        v___x_490_ = l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(v_s_486_);
        v___x_491_ = lean_uint64_mix_hash(v___x_489_, v___x_490_);
        return v___x_491_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash___boxed(
    mut v_x_492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_493_: u64 = 0;
    let mut v_r_494_: *mut LeanObject = core::ptr::null_mut();
    v_res_493_ = l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(v_x_492_);
    lean_dec_ref(v_x_492_);
    v_r_494_ = lean_box_uint64(v_res_493_);
    return v_r_494_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx(
    mut v_x_497_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_497_) {
        0 => {
            let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
            v___x_498_ = lean_unsigned_to_nat(0);
            return v___x_498_;
        }
        1 => {
            let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
            v___x_499_ = lean_unsigned_to_nat(1);
            return v___x_499_;
        }
        2 => {
            let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
            v___x_500_ = lean_unsigned_to_nat(2);
            return v___x_500_;
        }
        3 => {
            let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
            v___x_501_ = lean_unsigned_to_nat(3);
            return v___x_501_;
        }
        4 => {
            let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
            v___x_502_ = lean_unsigned_to_nat(4);
            return v___x_502_;
        }
        5 => {
            let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
            v___x_503_ = lean_unsigned_to_nat(5);
            return v___x_503_;
        }
        6 => {
            let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
            v___x_504_ = lean_unsigned_to_nat(6);
            return v___x_504_;
        }
        7 => {
            let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
            v___x_505_ = lean_unsigned_to_nat(7);
            return v___x_505_;
        }
        8 => {
            let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
            v___x_506_ = lean_unsigned_to_nat(8);
            return v___x_506_;
        }
        9 => {
            let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
            v___x_507_ = lean_unsigned_to_nat(9);
            return v___x_507_;
        }
        10 => {
            let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
            v___x_508_ = lean_unsigned_to_nat(10);
            return v___x_508_;
        }
        11 => {
            let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
            v___x_509_ = lean_unsigned_to_nat(11);
            return v___x_509_;
        }
        12 => {
            let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
            v___x_510_ = lean_unsigned_to_nat(12);
            return v___x_510_;
        }
        13 => {
            let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
            v___x_511_ = lean_unsigned_to_nat(13);
            return v___x_511_;
        }
        14 => {
            let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
            v___x_512_ = lean_unsigned_to_nat(14);
            return v___x_512_;
        }
        15 => {
            let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
            v___x_513_ = lean_unsigned_to_nat(15);
            return v___x_513_;
        }
        _ => {
            let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
            v___x_514_ = lean_unsigned_to_nat(16);
            return v___x_514_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx___boxed(
    mut v_x_515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_516_: *mut LeanObject = core::ptr::null_mut();
    v_res_516_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx(v_x_515_);
    lean_dec_ref(v_x_515_);
    return v_res_516_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
    mut v_t_517_: *mut LeanObject,
    mut v_k_518_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_517_) {
        0 => {
            let mut v_a_519_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_520_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ea_521_: *mut LeanObject = core::ptr::null_mut();
            let mut v_eb_522_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
            v_a_519_ = lean_ctor_get(v_t_517_, 0);
            lean_inc_ref(v_a_519_);
            v_b_520_ = lean_ctor_get(v_t_517_, 1);
            lean_inc_ref(v_b_520_);
            v_ea_521_ = lean_ctor_get(v_t_517_, 2);
            lean_inc_ref(v_ea_521_);
            v_eb_522_ = lean_ctor_get(v_t_517_, 3);
            lean_inc_ref(v_eb_522_);
            lean_dec_ref_known(v_t_517_, 4);
            v___x_523_ = lean_apply_4(v_k_518_, v_a_519_, v_b_520_, v_ea_521_, v_eb_522_);
            return v___x_523_;
        }
        4 => {
            let mut v_lhs_524_: u8 = 0;
            let mut v_c_u2081_525_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_526_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
            v_lhs_524_ = lean_ctor_get_uint8(
                v_t_517_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            v_c_u2081_525_ = lean_ctor_get(v_t_517_, 0);
            lean_inc_ref(v_c_u2081_525_);
            v_c_u2082_526_ = lean_ctor_get(v_t_517_, 1);
            lean_inc_ref(v_c_u2082_526_);
            lean_dec_ref_known(v_t_517_, 2);
            v___x_527_ = lean_box((v_lhs_524_) as usize);
            v___x_528_ = lean_apply_3(v_k_518_, v___x_527_, v_c_u2081_525_, v_c_u2082_526_);
            return v___x_528_;
        }
        5 => {
            let mut v_lhs_529_: u8 = 0;
            let mut v_s_530_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_531_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_532_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
            v_lhs_529_ = lean_ctor_get_uint8(
                v_t_517_,
                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
            );
            v_s_530_ = lean_ctor_get(v_t_517_, 0);
            lean_inc_ref(v_s_530_);
            v_c_u2081_531_ = lean_ctor_get(v_t_517_, 1);
            lean_inc_ref(v_c_u2081_531_);
            v_c_u2082_532_ = lean_ctor_get(v_t_517_, 2);
            lean_inc_ref(v_c_u2082_532_);
            lean_dec_ref_known(v_t_517_, 3);
            v___x_533_ = lean_box((v_lhs_529_) as usize);
            v___x_534_ = lean_apply_4(
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
            let mut v_s_536_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_537_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_538_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
            v_lhs_535_ = lean_ctor_get_uint8(
                v_t_517_,
                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
            );
            v_s_536_ = lean_ctor_get(v_t_517_, 0);
            lean_inc_ref(v_s_536_);
            v_c_u2081_537_ = lean_ctor_get(v_t_517_, 1);
            lean_inc_ref(v_c_u2081_537_);
            v_c_u2082_538_ = lean_ctor_get(v_t_517_, 2);
            lean_inc_ref(v_c_u2082_538_);
            lean_dec_ref_known(v_t_517_, 3);
            v___x_539_ = lean_box((v_lhs_535_) as usize);
            v___x_540_ = lean_apply_4(
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
            let mut v_s_542_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_543_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_544_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
            v_lhs_541_ = lean_ctor_get_uint8(
                v_t_517_,
                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
            );
            v_s_542_ = lean_ctor_get(v_t_517_, 0);
            lean_inc_ref(v_s_542_);
            v_c_u2081_543_ = lean_ctor_get(v_t_517_, 1);
            lean_inc_ref(v_c_u2081_543_);
            v_c_u2082_544_ = lean_ctor_get(v_t_517_, 2);
            lean_inc_ref(v_c_u2082_544_);
            lean_dec_ref_known(v_t_517_, 3);
            v___x_545_ = lean_box((v_lhs_541_) as usize);
            v___x_546_ = lean_apply_4(
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
            let mut v_s_u2081_548_: *mut LeanObject = core::ptr::null_mut();
            let mut v_s_u2082_549_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_550_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_551_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
            v_lhs_547_ = lean_ctor_get_uint8(
                v_t_517_,
                (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
            );
            v_s_u2081_548_ = lean_ctor_get(v_t_517_, 0);
            lean_inc_ref(v_s_u2081_548_);
            v_s_u2082_549_ = lean_ctor_get(v_t_517_, 1);
            lean_inc_ref(v_s_u2082_549_);
            v_c_u2081_550_ = lean_ctor_get(v_t_517_, 2);
            lean_inc_ref(v_c_u2081_550_);
            v_c_u2082_551_ = lean_ctor_get(v_t_517_, 3);
            lean_inc_ref(v_c_u2082_551_);
            lean_dec_ref_known(v_t_517_, 4);
            v___x_552_ = lean_box((v_lhs_547_) as usize);
            v___x_553_ = lean_apply_5(
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
            let mut v_r_u2081_554_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_555_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_u2082_556_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_557_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_558_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
            v_r_u2081_554_ = lean_ctor_get(v_t_517_, 0);
            lean_inc_ref(v_r_u2081_554_);
            v_c_555_ = lean_ctor_get(v_t_517_, 1);
            lean_inc_ref(v_c_555_);
            v_r_u2082_556_ = lean_ctor_get(v_t_517_, 2);
            lean_inc_ref(v_r_u2082_556_);
            v_c_u2081_557_ = lean_ctor_get(v_t_517_, 3);
            lean_inc_ref(v_c_u2081_557_);
            v_c_u2082_558_ = lean_ctor_get(v_t_517_, 4);
            lean_inc_ref(v_c_u2082_558_);
            lean_dec_ref_known(v_t_517_, 5);
            v___x_559_ = lean_apply_5(
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
            let mut v_p_560_: *mut LeanObject = core::ptr::null_mut();
            let mut v_s_561_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_562_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_563_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_564_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
            v_p_560_ = lean_ctor_get(v_t_517_, 0);
            lean_inc_ref(v_p_560_);
            v_s_561_ = lean_ctor_get(v_t_517_, 1);
            lean_inc_ref(v_s_561_);
            v_c_562_ = lean_ctor_get(v_t_517_, 2);
            lean_inc_ref(v_c_562_);
            v_c_u2081_563_ = lean_ctor_get(v_t_517_, 3);
            lean_inc_ref(v_c_u2081_563_);
            v_c_u2082_564_ = lean_ctor_get(v_t_517_, 4);
            lean_inc_ref(v_c_u2082_564_);
            lean_dec_ref_known(v_t_517_, 5);
            v___x_565_ = lean_apply_5(
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
            let mut v_x_566_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_567_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
            v_x_566_ = lean_ctor_get(v_t_517_, 0);
            lean_inc(v_x_566_);
            v_c_u2081_567_ = lean_ctor_get(v_t_517_, 1);
            lean_inc_ref(v_c_u2081_567_);
            lean_dec_ref_known(v_t_517_, 2);
            v___x_568_ = lean_apply_2(v_k_518_, v_x_566_, v_c_u2081_567_);
            return v___x_568_;
        }
        12 => {
            let mut v_x_569_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_570_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
            v_x_569_ = lean_ctor_get(v_t_517_, 0);
            lean_inc(v_x_569_);
            v_c_u2081_570_ = lean_ctor_get(v_t_517_, 1);
            lean_inc_ref(v_c_u2081_570_);
            lean_dec_ref_known(v_t_517_, 2);
            v___x_571_ = lean_apply_2(v_k_518_, v_x_569_, v_c_u2081_570_);
            return v___x_571_;
        }
        13 => {
            let mut v_x_572_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_573_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
            v_x_572_ = lean_ctor_get(v_t_517_, 0);
            lean_inc(v_x_572_);
            v_c_u2081_573_ = lean_ctor_get(v_t_517_, 1);
            lean_inc_ref(v_c_u2081_573_);
            lean_dec_ref_known(v_t_517_, 2);
            v___x_574_ = lean_apply_2(v_k_518_, v_x_572_, v_c_u2081_573_);
            return v___x_574_;
        }
        _ => {
            let mut v_c_575_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
            v_c_575_ = lean_ctor_get(v_t_517_, 0);
            lean_inc_ref(v_c_575_);
            lean_dec_ref(v_t_517_);
            v___x_576_ = lean_apply_1(v_k_518_, v_c_575_);
            return v___x_576_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim(
    mut v_motive__2_577_: *mut LeanObject,
    mut v_ctorIdx_578_: *mut LeanObject,
    mut v_t_579_: *mut LeanObject,
    mut v_h_580_: *mut LeanObject,
    mut v_k_581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    v___x_582_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_579_, v_k_581_);
    return v___x_582_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___boxed(
    mut v_motive__2_583_: *mut LeanObject,
    mut v_ctorIdx_584_: *mut LeanObject,
    mut v_t_585_: *mut LeanObject,
    mut v_h_586_: *mut LeanObject,
    mut v_k_587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_588_: *mut LeanObject = core::ptr::null_mut();
    v_res_588_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim(
        v_motive__2_583_,
        v_ctorIdx_584_,
        v_t_585_,
        v_h_586_,
        v_k_587_,
    );
    lean_dec(v_ctorIdx_584_);
    return v_res_588_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_core_elim___redArg(
    mut v_t_589_: *mut LeanObject,
    mut v_core_590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    v___x_591_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_589_, v_core_590_);
    return v___x_591_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_core_elim(
    mut v_motive__2_592_: *mut LeanObject,
    mut v_t_593_: *mut LeanObject,
    mut v_h_594_: *mut LeanObject,
    mut v_core_595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    v___x_596_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_593_, v_core_595_);
    return v___x_596_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup_elim___redArg(
    mut v_t_597_: *mut LeanObject,
    mut v_erase__dup_598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    v___x_599_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_597_, v_erase__dup_598_);
    return v___x_599_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup_elim(
    mut v_motive__2_600_: *mut LeanObject,
    mut v_t_601_: *mut LeanObject,
    mut v_h_602_: *mut LeanObject,
    mut v_erase__dup_603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    v___x_604_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_601_, v_erase__dup_603_);
    return v___x_604_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase0_elim___redArg(
    mut v_t_605_: *mut LeanObject,
    mut v_erase0_606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    v___x_607_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_605_, v_erase0_606_);
    return v___x_607_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase0_elim(
    mut v_motive__2_608_: *mut LeanObject,
    mut v_t_609_: *mut LeanObject,
    mut v_h_610_: *mut LeanObject,
    mut v_erase0_611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    v___x_612_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_609_, v_erase0_611_);
    return v___x_612_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_swap_elim___redArg(
    mut v_t_613_: *mut LeanObject,
    mut v_swap_614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    v___x_615_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_613_, v_swap_614_);
    return v___x_615_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_swap_elim(
    mut v_motive__2_616_: *mut LeanObject,
    mut v_t_617_: *mut LeanObject,
    mut v_h_618_: *mut LeanObject,
    mut v_swap_619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    v___x_620_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_617_, v_swap_619_);
    return v___x_620_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__exact_elim___redArg(
    mut v_t_621_: *mut LeanObject,
    mut v_simp__exact_622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    v___x_623_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_621_, v_simp__exact_622_);
    return v___x_623_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__exact_elim(
    mut v_motive__2_624_: *mut LeanObject,
    mut v_t_625_: *mut LeanObject,
    mut v_h_626_: *mut LeanObject,
    mut v_simp__exact_627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    v___x_628_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_625_, v_simp__exact_627_);
    return v___x_628_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__ac_elim___redArg(
    mut v_t_629_: *mut LeanObject,
    mut v_simp__ac_630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    v___x_631_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_629_, v_simp__ac_630_);
    return v___x_631_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__ac_elim(
    mut v_motive__2_632_: *mut LeanObject,
    mut v_t_633_: *mut LeanObject,
    mut v_h_634_: *mut LeanObject,
    mut v_simp__ac_635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    v___x_636_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_633_, v_simp__ac_635_);
    return v___x_636_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__suffix_elim___redArg(
    mut v_t_637_: *mut LeanObject,
    mut v_simp__suffix_638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    v___x_639_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_637_, v_simp__suffix_638_);
    return v___x_639_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__suffix_elim(
    mut v_motive__2_640_: *mut LeanObject,
    mut v_t_641_: *mut LeanObject,
    mut v_h_642_: *mut LeanObject,
    mut v_simp__suffix_643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    v___x_644_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_641_, v_simp__suffix_643_);
    return v___x_644_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__prefix_elim___redArg(
    mut v_t_645_: *mut LeanObject,
    mut v_simp__prefix_646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    v___x_647_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_645_, v_simp__prefix_646_);
    return v___x_647_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__prefix_elim(
    mut v_motive__2_648_: *mut LeanObject,
    mut v_t_649_: *mut LeanObject,
    mut v_h_650_: *mut LeanObject,
    mut v_simp__prefix_651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    v___x_652_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_649_, v_simp__prefix_651_);
    return v___x_652_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__middle_elim___redArg(
    mut v_t_653_: *mut LeanObject,
    mut v_simp__middle_654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    v___x_655_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_653_, v_simp__middle_654_);
    return v___x_655_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_simp__middle_elim(
    mut v_motive__2_656_: *mut LeanObject,
    mut v_t_657_: *mut LeanObject,
    mut v_h_658_: *mut LeanObject,
    mut v_simp__middle_659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    v___x_660_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_657_, v_simp__middle_659_);
    return v___x_660_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac_elim___redArg(
    mut v_t_661_: *mut LeanObject,
    mut v_superpose__ac_662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    v___x_663_ =
        l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_661_, v_superpose__ac_662_);
    return v___x_663_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac_elim(
    mut v_motive__2_664_: *mut LeanObject,
    mut v_t_665_: *mut LeanObject,
    mut v_h_666_: *mut LeanObject,
    mut v_superpose__ac_667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    v___x_668_ =
        l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_665_, v_superpose__ac_667_);
    return v___x_668_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose_elim___redArg(
    mut v_t_669_: *mut LeanObject,
    mut v_superpose_670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    v___x_671_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_669_, v_superpose_670_);
    return v___x_671_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose_elim(
    mut v_motive__2_672_: *mut LeanObject,
    mut v_t_673_: *mut LeanObject,
    mut v_h_674_: *mut LeanObject,
    mut v_superpose_675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    v___x_676_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_673_, v_superpose_675_);
    return v___x_676_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac__idempotent_elim___redArg(
    mut v_t_677_: *mut LeanObject,
    mut v_superpose__ac__idempotent_678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    v___x_679_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
        v_t_677_,
        v_superpose__ac__idempotent_678_,
    );
    return v___x_679_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac__idempotent_elim(
    mut v_motive__2_680_: *mut LeanObject,
    mut v_t_681_: *mut LeanObject,
    mut v_h_682_: *mut LeanObject,
    mut v_superpose__ac__idempotent_683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    v___x_684_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
        v_t_681_,
        v_superpose__ac__idempotent_683_,
    );
    return v___x_684_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__head__idempotent_elim___redArg(
    mut v_t_685_: *mut LeanObject,
    mut v_superpose__head__idempotent_686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    v___x_687_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
        v_t_685_,
        v_superpose__head__idempotent_686_,
    );
    return v___x_687_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__head__idempotent_elim(
    mut v_motive__2_688_: *mut LeanObject,
    mut v_t_689_: *mut LeanObject,
    mut v_h_690_: *mut LeanObject,
    mut v_superpose__head__idempotent_691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    v___x_692_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
        v_t_689_,
        v_superpose__head__idempotent_691_,
    );
    return v___x_692_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__tail__idempotent_elim___redArg(
    mut v_t_693_: *mut LeanObject,
    mut v_superpose__tail__idempotent_694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    v___x_695_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
        v_t_693_,
        v_superpose__tail__idempotent_694_,
    );
    return v___x_695_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__tail__idempotent_elim(
    mut v_motive__2_696_: *mut LeanObject,
    mut v_t_697_: *mut LeanObject,
    mut v_h_698_: *mut LeanObject,
    mut v_superpose__tail__idempotent_699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    v___x_700_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(
        v_t_697_,
        v_superpose__tail__idempotent_699_,
    );
    return v___x_700_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_refl_elim___redArg(
    mut v_t_701_: *mut LeanObject,
    mut v_refl_702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    v___x_703_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_701_, v_refl_702_);
    return v___x_703_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_refl_elim(
    mut v_motive__2_704_: *mut LeanObject,
    mut v_t_705_: *mut LeanObject,
    mut v_h_706_: *mut LeanObject,
    mut v_refl_707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    v___x_708_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_705_, v_refl_707_);
    return v___x_708_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup__rhs_elim___redArg(
    mut v_t_709_: *mut LeanObject,
    mut v_erase__dup__rhs_710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    v___x_711_ =
        l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_709_, v_erase__dup__rhs_710_);
    return v___x_711_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup__rhs_elim(
    mut v_motive__2_712_: *mut LeanObject,
    mut v_t_713_: *mut LeanObject,
    mut v_h_714_: *mut LeanObject,
    mut v_erase__dup__rhs_715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    v___x_716_ =
        l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_713_, v_erase__dup__rhs_715_);
    return v___x_716_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase0__rhs_elim___redArg(
    mut v_t_717_: *mut LeanObject,
    mut v_erase0__rhs_718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    v___x_719_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_717_, v_erase0__rhs_718_);
    return v___x_719_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstrProof_erase0__rhs_elim(
    mut v_motive__2_720_: *mut LeanObject,
    mut v_t_721_: *mut LeanObject,
    mut v_h_722_: *mut LeanObject,
    mut v_erase0__rhs_723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    v___x_724_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_721_, v_erase0__rhs_723_);
    return v___x_724_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2() -> *mut LeanObject
{
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    v___x_728_ = lean_box(0);
    v___x_729_ = l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1;
    v___x_730_ = l_Lean_Expr_const___override(v___x_729_, v___x_728_);
    return v___x_730_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3() -> *mut LeanObject
{
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    v___x_731_ = l_Lean_Grind_AC_instInhabitedExpr_default;
    v___x_732_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2,
    );
    v___x_733_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_733_, 0, v___x_732_);
    lean_ctor_set(v___x_733_, 1, v___x_732_);
    lean_ctor_set(v___x_733_, 2, v___x_731_);
    lean_ctor_set(v___x_733_, 3, v___x_731_);
    return v___x_733_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof() -> *mut LeanObject {
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    v___x_734_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3,
    );
    return v___x_734_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0() -> *mut LeanObject {
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    v___x_735_ = lean_unsigned_to_nat(0);
    v___x_736_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3,
    );
    v___x_737_ = l_Lean_Grind_AC_instInhabitedSeq_default;
    v___x_738_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_738_, 0, v___x_737_);
    lean_ctor_set(v___x_738_, 1, v___x_737_);
    lean_ctor_set(v___x_738_, 2, v___x_736_);
    lean_ctor_set(v___x_738_, 3, v___x_735_);
    return v___x_738_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr() -> *mut LeanObject {
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    v___x_739_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0,
    );
    return v___x_739_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_compare(
    mut v_c_u2081_740_: *mut LeanObject,
    mut v_c_u2082_741_: *mut LeanObject,
) -> u8 {
    let mut v_lhs_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: u8 = 0;
    v_lhs_742_ = lean_ctor_get(v_c_u2081_740_, 0);
    v_id_743_ = lean_ctor_get(v_c_u2081_740_, 3);
    v_lhs_744_ = lean_ctor_get(v_c_u2082_741_, 0);
    v_id_745_ = lean_ctor_get(v_c_u2082_741_, 3);
    v___x_746_ = l_Lean_Grind_AC_Seq_length(v_lhs_742_);
    v___x_747_ = l_Lean_Grind_AC_Seq_length(v_lhs_744_);
    v___x_748_ = lean_nat_dec_lt(v___x_746_, v___x_747_);
    if v___x_748_ == 0 {
        let mut v___x_749_: u8 = 0;
        v___x_749_ = lean_nat_dec_eq(v___x_746_, v___x_747_);
        lean_dec(v___x_747_);
        lean_dec(v___x_746_);
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
        lean_dec(v___x_747_);
        lean_dec(v___x_746_);
        v___x_756_ = 0;
        return v___x_756_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_compare___boxed(
    mut v_c_u2081_757_: *mut LeanObject,
    mut v_c_u2082_758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_759_: u8 = 0;
    let mut v_r_760_: *mut LeanObject = core::ptr::null_mut();
    v_res_759_ = l_Lean_Meta_Grind_AC_EqCnstr_compare(v_c_u2081_757_, v_c_u2082_758_);
    lean_dec_ref(v_c_u2082_758_);
    lean_dec_ref(v_c_u2081_757_);
    v_r_760_ = lean_box((v_res_759_) as usize);
    return v_r_760_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx(
    mut v_x_761_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_761_) {
        0 => {
            let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
            v___x_762_ = lean_unsigned_to_nat(0);
            return v___x_762_;
        }
        1 => {
            let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
            v___x_763_ = lean_unsigned_to_nat(1);
            return v___x_763_;
        }
        2 => {
            let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
            v___x_764_ = lean_unsigned_to_nat(2);
            return v___x_764_;
        }
        3 => {
            let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
            v___x_765_ = lean_unsigned_to_nat(3);
            return v___x_765_;
        }
        4 => {
            let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
            v___x_766_ = lean_unsigned_to_nat(4);
            return v___x_766_;
        }
        5 => {
            let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
            v___x_767_ = lean_unsigned_to_nat(5);
            return v___x_767_;
        }
        6 => {
            let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
            v___x_768_ = lean_unsigned_to_nat(6);
            return v___x_768_;
        }
        _ => {
            let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
            v___x_769_ = lean_unsigned_to_nat(7);
            return v___x_769_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx___boxed(
    mut v_x_770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_771_: *mut LeanObject = core::ptr::null_mut();
    v_res_771_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx(v_x_770_);
    lean_dec_ref(v_x_770_);
    return v_res_771_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(
    mut v_t_772_: *mut LeanObject,
    mut v_k_773_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_772_) {
        0 => {
            let mut v_a_774_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_775_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ea_776_: *mut LeanObject = core::ptr::null_mut();
            let mut v_eb_777_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
            v_a_774_ = lean_ctor_get(v_t_772_, 0);
            lean_inc_ref(v_a_774_);
            v_b_775_ = lean_ctor_get(v_t_772_, 1);
            lean_inc_ref(v_b_775_);
            v_ea_776_ = lean_ctor_get(v_t_772_, 2);
            lean_inc_ref(v_ea_776_);
            v_eb_777_ = lean_ctor_get(v_t_772_, 3);
            lean_inc_ref(v_eb_777_);
            lean_dec_ref_known(v_t_772_, 4);
            v___x_778_ = lean_apply_4(v_k_773_, v_a_774_, v_b_775_, v_ea_776_, v_eb_777_);
            return v___x_778_;
        }
        1 => {
            let mut v_c_779_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
            v_c_779_ = lean_ctor_get(v_t_772_, 0);
            lean_inc_ref(v_c_779_);
            lean_dec_ref_known(v_t_772_, 1);
            v___x_780_ = lean_apply_1(v_k_773_, v_c_779_);
            return v___x_780_;
        }
        2 => {
            let mut v_c_781_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
            v_c_781_ = lean_ctor_get(v_t_772_, 0);
            lean_inc_ref(v_c_781_);
            lean_dec_ref_known(v_t_772_, 1);
            v___x_782_ = lean_apply_1(v_k_773_, v_c_781_);
            return v___x_782_;
        }
        3 => {
            let mut v_lhs_783_: u8 = 0;
            let mut v_c_u2081_784_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_785_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
            v_lhs_783_ = lean_ctor_get_uint8(
                v_t_772_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            v_c_u2081_784_ = lean_ctor_get(v_t_772_, 0);
            lean_inc_ref(v_c_u2081_784_);
            v_c_u2082_785_ = lean_ctor_get(v_t_772_, 1);
            lean_inc_ref(v_c_u2082_785_);
            lean_dec_ref_known(v_t_772_, 2);
            v___x_786_ = lean_box((v_lhs_783_) as usize);
            v___x_787_ = lean_apply_3(v_k_773_, v___x_786_, v_c_u2081_784_, v_c_u2082_785_);
            return v___x_787_;
        }
        7 => {
            let mut v_lhs_788_: u8 = 0;
            let mut v_s_u2081_789_: *mut LeanObject = core::ptr::null_mut();
            let mut v_s_u2082_790_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_791_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_792_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
            v_lhs_788_ = lean_ctor_get_uint8(
                v_t_772_,
                (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
            );
            v_s_u2081_789_ = lean_ctor_get(v_t_772_, 0);
            lean_inc_ref(v_s_u2081_789_);
            v_s_u2082_790_ = lean_ctor_get(v_t_772_, 1);
            lean_inc_ref(v_s_u2082_790_);
            v_c_u2081_791_ = lean_ctor_get(v_t_772_, 2);
            lean_inc_ref(v_c_u2081_791_);
            v_c_u2082_792_ = lean_ctor_get(v_t_772_, 3);
            lean_inc_ref(v_c_u2082_792_);
            lean_dec_ref_known(v_t_772_, 4);
            v___x_793_ = lean_box((v_lhs_788_) as usize);
            v___x_794_ = lean_apply_5(
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
            let mut v_s_796_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_797_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_798_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
            v_lhs_795_ = lean_ctor_get_uint8(
                v_t_772_,
                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
            );
            v_s_796_ = lean_ctor_get(v_t_772_, 0);
            lean_inc_ref(v_s_796_);
            v_c_u2081_797_ = lean_ctor_get(v_t_772_, 1);
            lean_inc_ref(v_c_u2081_797_);
            v_c_u2082_798_ = lean_ctor_get(v_t_772_, 2);
            lean_inc_ref(v_c_u2082_798_);
            lean_dec_ref(v_t_772_);
            v___x_799_ = lean_box((v_lhs_795_) as usize);
            v___x_800_ = lean_apply_4(
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
    mut v_motive__2_801_: *mut LeanObject,
    mut v_ctorIdx_802_: *mut LeanObject,
    mut v_t_803_: *mut LeanObject,
    mut v_h_804_: *mut LeanObject,
    mut v_k_805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    v___x_806_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_803_, v_k_805_);
    return v___x_806_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___boxed(
    mut v_motive__2_807_: *mut LeanObject,
    mut v_ctorIdx_808_: *mut LeanObject,
    mut v_t_809_: *mut LeanObject,
    mut v_h_810_: *mut LeanObject,
    mut v_k_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_812_: *mut LeanObject = core::ptr::null_mut();
    v_res_812_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim(
        v_motive__2_807_,
        v_ctorIdx_808_,
        v_t_809_,
        v_h_810_,
        v_k_811_,
    );
    lean_dec(v_ctorIdx_808_);
    return v_res_812_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_core_elim___redArg(
    mut v_t_813_: *mut LeanObject,
    mut v_core_814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    v___x_815_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_813_, v_core_814_);
    return v___x_815_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_core_elim(
    mut v_motive__2_816_: *mut LeanObject,
    mut v_t_817_: *mut LeanObject,
    mut v_h_818_: *mut LeanObject,
    mut v_core_819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    v___x_820_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_817_, v_core_819_);
    return v___x_820_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase__dup_elim___redArg(
    mut v_t_821_: *mut LeanObject,
    mut v_erase__dup_822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    v___x_823_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_821_, v_erase__dup_822_);
    return v___x_823_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase__dup_elim(
    mut v_motive__2_824_: *mut LeanObject,
    mut v_t_825_: *mut LeanObject,
    mut v_h_826_: *mut LeanObject,
    mut v_erase__dup_827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    v___x_828_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_825_, v_erase__dup_827_);
    return v___x_828_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase0_elim___redArg(
    mut v_t_829_: *mut LeanObject,
    mut v_erase0_830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    v___x_831_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_829_, v_erase0_830_);
    return v___x_831_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase0_elim(
    mut v_motive__2_832_: *mut LeanObject,
    mut v_t_833_: *mut LeanObject,
    mut v_h_834_: *mut LeanObject,
    mut v_erase0_835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    v___x_836_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_833_, v_erase0_835_);
    return v___x_836_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__exact_elim___redArg(
    mut v_t_837_: *mut LeanObject,
    mut v_simp__exact_838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    v___x_839_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_837_, v_simp__exact_838_);
    return v___x_839_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__exact_elim(
    mut v_motive__2_840_: *mut LeanObject,
    mut v_t_841_: *mut LeanObject,
    mut v_h_842_: *mut LeanObject,
    mut v_simp__exact_843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    v___x_844_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_841_, v_simp__exact_843_);
    return v___x_844_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__ac_elim___redArg(
    mut v_t_845_: *mut LeanObject,
    mut v_simp__ac_846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    v___x_847_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_845_, v_simp__ac_846_);
    return v___x_847_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__ac_elim(
    mut v_motive__2_848_: *mut LeanObject,
    mut v_t_849_: *mut LeanObject,
    mut v_h_850_: *mut LeanObject,
    mut v_simp__ac_851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    v___x_852_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_849_, v_simp__ac_851_);
    return v___x_852_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__suffix_elim___redArg(
    mut v_t_853_: *mut LeanObject,
    mut v_simp__suffix_854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    v___x_855_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_853_, v_simp__suffix_854_);
    return v___x_855_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__suffix_elim(
    mut v_motive__2_856_: *mut LeanObject,
    mut v_t_857_: *mut LeanObject,
    mut v_h_858_: *mut LeanObject,
    mut v_simp__suffix_859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    v___x_860_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_857_, v_simp__suffix_859_);
    return v___x_860_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__prefix_elim___redArg(
    mut v_t_861_: *mut LeanObject,
    mut v_simp__prefix_862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    v___x_863_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_861_, v_simp__prefix_862_);
    return v___x_863_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__prefix_elim(
    mut v_motive__2_864_: *mut LeanObject,
    mut v_t_865_: *mut LeanObject,
    mut v_h_866_: *mut LeanObject,
    mut v_simp__prefix_867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    v___x_868_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_865_, v_simp__prefix_867_);
    return v___x_868_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__middle_elim___redArg(
    mut v_t_869_: *mut LeanObject,
    mut v_simp__middle_870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    v___x_871_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_869_, v_simp__middle_870_);
    return v___x_871_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__middle_elim(
    mut v_motive__2_872_: *mut LeanObject,
    mut v_t_873_: *mut LeanObject,
    mut v_h_874_: *mut LeanObject,
    mut v_simp__middle_875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    v___x_876_ =
        l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_873_, v_simp__middle_875_);
    return v___x_876_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0() -> *mut LeanObject
{
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    v___x_877_ = lean_unsigned_to_nat(32);
    v___x_878_ = lean_mk_empty_array_with_capacity(v___x_877_);
    v___x_879_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_879_, 0, v___x_878_);
    return v___x_879_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1() -> *mut LeanObject
{
    let mut v___x_880_: usize = 0;
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    v___x_880_ = 5usize;
    v___x_881_ = lean_unsigned_to_nat(0);
    v___x_882_ = lean_unsigned_to_nat(32);
    v___x_883_ = lean_mk_empty_array_with_capacity(v___x_882_);
    v___x_884_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0,
    );
    v___x_885_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_885_, 0, v___x_884_);
    lean_ctor_set(v___x_885_, 1, v___x_883_);
    lean_ctor_set(v___x_885_, 2, v___x_881_);
    lean_ctor_set(v___x_885_, 3, v___x_881_);
    lean_ctor_set_usize(v___x_885_, 4, v___x_880_);
    return v___x_885_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2() -> *mut LeanObject
{
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    v___x_886_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_886_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3() -> *mut LeanObject
{
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    v___x_887_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2,
    );
    v___x_888_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_888_, 0, v___x_887_);
    return v___x_888_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4() -> *mut LeanObject
{
    let mut v___x_889_: u8 = 0;
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    v___x_889_ = 0;
    v___x_890_ = lean_box(0);
    v___x_891_ = lean_box(1);
    v___x_892_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3,
    );
    v___x_893_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1,
    );
    v___x_894_ = lean_box(0);
    v___x_895_ = lean_box(0);
    v___x_896_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2,
    );
    v___x_897_ = lean_unsigned_to_nat(0);
    v___x_898_ = lean_alloc_ctor(0, 17, (1) as u32);
    lean_ctor_set(v___x_898_, 0, v___x_897_);
    lean_ctor_set(v___x_898_, 1, v___x_896_);
    lean_ctor_set(v___x_898_, 2, v___x_895_);
    lean_ctor_set(v___x_898_, 3, v___x_896_);
    lean_ctor_set(v___x_898_, 4, v___x_894_);
    lean_ctor_set(v___x_898_, 5, v___x_896_);
    lean_ctor_set(v___x_898_, 6, v___x_894_);
    lean_ctor_set(v___x_898_, 7, v___x_894_);
    lean_ctor_set(v___x_898_, 8, v___x_894_);
    lean_ctor_set(v___x_898_, 9, v___x_897_);
    lean_ctor_set(v___x_898_, 10, v___x_893_);
    lean_ctor_set(v___x_898_, 11, v___x_892_);
    lean_ctor_set(v___x_898_, 12, v___x_892_);
    lean_ctor_set(v___x_898_, 13, v___x_893_);
    lean_ctor_set(v___x_898_, 14, v___x_891_);
    lean_ctor_set(v___x_898_, 15, v___x_890_);
    lean_ctor_set(v___x_898_, 16, v___x_893_);
    lean_ctor_set_uint8(
        v___x_898_,
        (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
        v___x_889_,
    );
    return v___x_898_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default() -> *mut LeanObject {
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    v___x_899_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4,
    );
    return v___x_899_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedStruct() -> *mut LeanObject {
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    v___x_900_ = l_Lean_Meta_Grind_AC_instInhabitedStruct_default;
    return v___x_900_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1() -> *mut LeanObject
{
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    v___x_903_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_903_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2() -> *mut LeanObject
{
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    v___x_904_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1,
    );
    v___x_905_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_905_, 0, v___x_904_);
    return v___x_905_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3() -> *mut LeanObject
{
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    v___x_906_ = lean_unsigned_to_nat(0);
    v___x_907_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2,
    );
    v___x_908_ = l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__0;
    v___x_909_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_909_, 0, v___x_908_);
    lean_ctor_set(v___x_909_, 1, v___x_907_);
    lean_ctor_set(v___x_909_, 2, v___x_907_);
    lean_ctor_set(v___x_909_, 3, v___x_906_);
    return v___x_909_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedState_default() -> *mut LeanObject {
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    v___x_910_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3,
    );
    return v___x_910_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instInhabitedState() -> *mut LeanObject {
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    v___x_911_ = l_Lean_Meta_Grind_AC_instInhabitedState_default;
    return v___x_911_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(
    mut v___x_912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    v___x_914_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_914_, 0, v___x_912_);
    return v___x_914_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed(
    mut v___x_915_: *mut LeanObject,
    mut v___y_916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_917_: *mut LeanObject = core::ptr::null_mut();
    v_res_917_ = l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(v___x_915_);
    return v_res_917_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_919_: *mut LeanObject = core::ptr::null_mut();
    v___x_918_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3_once),
        _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3,
    );
    v___f_919_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_919_, 0, v___x_918_);
    return v___f_919_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    v___f_921_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_);
    v___x_922_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_921_);
    return v___x_922_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed(
    mut v_a_923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_924_: *mut LeanObject = core::ptr::null_mut();
    v_res_924_ = l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_();
    return v_res_924_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_AC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof =
        _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof();
    lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof);
    l_Lean_Meta_Grind_AC_instInhabitedEqCnstr = _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr();
    lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedEqCnstr);
    l_Lean_Meta_Grind_AC_instInhabitedStruct_default =
        _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default();
    lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedStruct_default);
    l_Lean_Meta_Grind_AC_instInhabitedStruct = _init_l_Lean_Meta_Grind_AC_instInhabitedStruct();
    lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedStruct);
    l_Lean_Meta_Grind_AC_instInhabitedState_default =
        _init_l_Lean_Meta_Grind_AC_instInhabitedState_default();
    lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedState_default);
    l_Lean_Meta_Grind_AC_instInhabitedState = _init_l_Lean_Meta_Grind_AC_instInhabitedState();
    lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedState);
    res = l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Grind_AC_acExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_Grind_AC_acExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_AC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_HashMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
}
