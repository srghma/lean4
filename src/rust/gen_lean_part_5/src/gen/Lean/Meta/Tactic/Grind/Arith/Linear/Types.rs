// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Types
// Imports: Init.Grind.Ring.CommSolver Init.Grind.Ordered.Linarith Lean.Meta.Tactic.Grind.Types
use crate::ffi::{
    lean_int_dec_lt, lean_mk_empty_array_with_capacity, lean_nat_abs, lean_nat_add, lean_nat_mul,
    lean_nat_sub, lean_nat_to_int, lean_uint64_mix_hash, lean_uint64_of_nat,
};
use crate::r#gen::Init::Grind::Ordered::Linarith::{
    initialize_Init_Grind_Ordered_Linarith, runtime_initialize_Init_Grind_Ordered_Linarith,
};
use crate::r#gen::Init::Grind::Ring::CommSolver::{
    initialize_Init_Grind_Ring_CommSolver, runtime_initialize_Init_Grind_Ring_CommSolver,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::l_Lean_Expr_const___override;
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_registerSolverExtension___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
static mut l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__0_value:
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
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__0_value
        ) as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__0_value:
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
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedState: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Linear_linearExt: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0()
-> *mut leanh::LeanObject {
    let mut v_natZero_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_natZero_757_ = leanh::lean_unsigned_to_nat(0);
    v_intZero_758_ = lean_nat_to_int(v_natZero_757_);
    return v_intZero_758_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash(
    mut v_x_759_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_760_: u64 = 0;
    let mut v_k_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: u64 = 0;
    let mut v___y_766_: u64 = 0;
    let mut v___x_767_: u64 = 0;
    let mut v___x_768_: u64 = 0;
    let mut v___x_769_: u64 = 0;
    let mut v___x_770_: u64 = 0;
    let mut v___x_771_: u64 = 0;
    let mut v_intZero_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_773_: u8 = 0;
    let mut v_a_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: u64 = 0;
    let mut v_abs_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_759_) == 0 {
                    v___x_760_ = 0u64;
                    return v___x_760_;
                } else {
                    v_k_761_ = leanh::lean_ctor_get(v_x_759_, 0);
                    v_v_762_ = leanh::lean_ctor_get(v_x_759_, 1);
                    v_p_763_ = leanh::lean_ctor_get(v_x_759_, 2);
                    v___x_764_ = 1u64;
                    v_intZero_772_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0_once), _init_l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0);
                    v_isNeg_773_ = lean_int_dec_lt(v_k_761_, v_intZero_772_);
                    if v_isNeg_773_ == 0 {
                        v_a_774_ = lean_nat_abs(v_k_761_);
                        v___x_775_ = leanh::lean_unsigned_to_nat(2);
                        v___x_776_ = lean_nat_mul(v___x_775_, v_a_774_);
                        leanh::lean_dec(v_a_774_);
                        v___x_777_ = lean_uint64_of_nat(v___x_776_);
                        leanh::lean_dec(v___x_776_);
                        v___y_766_ = v___x_777_;
                        state = 1;
                        continue;
                    } else {
                        v_abs_778_ = lean_nat_abs(v_k_761_);
                        v_one_779_ = leanh::lean_unsigned_to_nat(1);
                        v_a_780_ = lean_nat_sub(v_abs_778_, v_one_779_);
                        leanh::lean_dec(v_abs_778_);
                        v___x_781_ = leanh::lean_unsigned_to_nat(2);
                        v___x_782_ = lean_nat_mul(v___x_781_, v_a_780_);
                        leanh::lean_dec(v_a_780_);
                        v___x_783_ = lean_nat_add(v___x_782_, v_one_779_);
                        leanh::lean_dec(v___x_782_);
                        v___x_784_ = lean_uint64_of_nat(v___x_783_);
                        leanh::lean_dec(v___x_783_);
                        v___y_766_ = v___x_784_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_767_ = lean_uint64_mix_hash(v___x_764_, v___y_766_);
                v___x_768_ = lean_uint64_of_nat(v_v_762_);
                v___x_769_ = lean_uint64_mix_hash(v___x_767_, v___x_768_);
                v___x_770_ = l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash(v_p_763_);
                v___x_771_ = lean_uint64_mix_hash(v___x_769_, v___x_770_);
                return v___x_771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___boxed(
    mut v_x_785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_786_: u64 = 0;
    let mut v_r_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_786_ = l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash(v_x_785_);
    leanh::lean_dec(v_x_785_);
    v_r_787_ = leanh::lean_box_uint64(v_res_786_);
    return v_r_787_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(
    mut v_x_790_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_791_: u64 = 0;
    let mut v_i_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: u64 = 0;
    let mut v___x_794_: u64 = 0;
    let mut v___x_795_: u64 = 0;
    let mut v_a_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: u64 = 0;
    let mut v___x_799_: u64 = 0;
    let mut v___x_800_: u64 = 0;
    let mut v___x_801_: u64 = 0;
    let mut v___x_802_: u64 = 0;
    let mut v_a_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: u64 = 0;
    let mut v___x_806_: u64 = 0;
    let mut v___x_807_: u64 = 0;
    let mut v___x_808_: u64 = 0;
    let mut v___x_809_: u64 = 0;
    let mut v_a_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: u64 = 0;
    let mut v___x_812_: u64 = 0;
    let mut v___x_813_: u64 = 0;
    let mut v_k_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: u64 = 0;
    let mut v___x_817_: u64 = 0;
    let mut v___x_818_: u64 = 0;
    let mut v___x_819_: u64 = 0;
    let mut v___x_820_: u64 = 0;
    let mut v_k_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: u64 = 0;
    let mut v___y_825_: u64 = 0;
    let mut v___x_826_: u64 = 0;
    let mut v___x_827_: u64 = 0;
    let mut v___x_828_: u64 = 0;
    let mut v_intZero_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_830_: u8 = 0;
    let mut v_a_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: u64 = 0;
    let mut v_abs_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_790_) {
                0 => {
                    v___x_791_ = 0u64;
                    return v___x_791_;
                }
                1 => {
                    v_i_792_ = leanh::lean_ctor_get(v_x_790_, 0);
                    v___x_793_ = 1u64;
                    v___x_794_ = lean_uint64_of_nat(v_i_792_);
                    v___x_795_ = lean_uint64_mix_hash(v___x_793_, v___x_794_);
                    return v___x_795_;
                }
                2 => {
                    v_a_796_ = leanh::lean_ctor_get(v_x_790_, 0);
                    v_b_797_ = leanh::lean_ctor_get(v_x_790_, 1);
                    v___x_798_ = 2u64;
                    v___x_799_ =
                        l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_a_796_);
                    v___x_800_ = lean_uint64_mix_hash(v___x_798_, v___x_799_);
                    v___x_801_ =
                        l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_b_797_);
                    v___x_802_ = lean_uint64_mix_hash(v___x_800_, v___x_801_);
                    return v___x_802_;
                }
                3 => {
                    v_a_803_ = leanh::lean_ctor_get(v_x_790_, 0);
                    v_b_804_ = leanh::lean_ctor_get(v_x_790_, 1);
                    v___x_805_ = 3u64;
                    v___x_806_ =
                        l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_a_803_);
                    v___x_807_ = lean_uint64_mix_hash(v___x_805_, v___x_806_);
                    v___x_808_ =
                        l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_b_804_);
                    v___x_809_ = lean_uint64_mix_hash(v___x_807_, v___x_808_);
                    return v___x_809_;
                }
                4 => {
                    v_a_810_ = leanh::lean_ctor_get(v_x_790_, 0);
                    v___x_811_ = 4u64;
                    v___x_812_ =
                        l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_a_810_);
                    v___x_813_ = lean_uint64_mix_hash(v___x_811_, v___x_812_);
                    return v___x_813_;
                }
                5 => {
                    v_k_814_ = leanh::lean_ctor_get(v_x_790_, 0);
                    v_a_815_ = leanh::lean_ctor_get(v_x_790_, 1);
                    v___x_816_ = 5u64;
                    v___x_817_ = lean_uint64_of_nat(v_k_814_);
                    v___x_818_ = lean_uint64_mix_hash(v___x_816_, v___x_817_);
                    v___x_819_ =
                        l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_a_815_);
                    v___x_820_ = lean_uint64_mix_hash(v___x_818_, v___x_819_);
                    return v___x_820_;
                }
                _ => {
                    v_k_821_ = leanh::lean_ctor_get(v_x_790_, 0);
                    v_a_822_ = leanh::lean_ctor_get(v_x_790_, 1);
                    v___x_823_ = 6u64;
                    v_intZero_829_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0_once), _init_l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0);
                    v_isNeg_830_ = lean_int_dec_lt(v_k_821_, v_intZero_829_);
                    if v_isNeg_830_ == 0 {
                        v_a_831_ = lean_nat_abs(v_k_821_);
                        v___x_832_ = leanh::lean_unsigned_to_nat(2);
                        v___x_833_ = lean_nat_mul(v___x_832_, v_a_831_);
                        leanh::lean_dec(v_a_831_);
                        v___x_834_ = lean_uint64_of_nat(v___x_833_);
                        leanh::lean_dec(v___x_833_);
                        v___y_825_ = v___x_834_;
                        state = 1;
                        continue;
                    } else {
                        v_abs_835_ = lean_nat_abs(v_k_821_);
                        v_one_836_ = leanh::lean_unsigned_to_nat(1);
                        v_a_837_ = lean_nat_sub(v_abs_835_, v_one_836_);
                        leanh::lean_dec(v_abs_835_);
                        v___x_838_ = leanh::lean_unsigned_to_nat(2);
                        v___x_839_ = lean_nat_mul(v___x_838_, v_a_837_);
                        leanh::lean_dec(v_a_837_);
                        v___x_840_ = lean_nat_add(v___x_839_, v_one_836_);
                        leanh::lean_dec(v___x_839_);
                        v___x_841_ = lean_uint64_of_nat(v___x_840_);
                        leanh::lean_dec(v___x_840_);
                        v___y_825_ = v___x_841_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => {
                v___x_826_ = lean_uint64_mix_hash(v___x_823_, v___y_825_);
                v___x_827_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_a_822_);
                v___x_828_ = lean_uint64_mix_hash(v___x_826_, v___x_827_);
                return v___x_828_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash___boxed(
    mut v_x_842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_843_: u64 = 0;
    let mut v_r_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_843_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_x_842_);
    leanh::lean_dec(v_x_842_);
    v_r_844_ = leanh::lean_box_uint64(v_res_843_);
    return v_r_844_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorIdx(
    mut v_x_847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_847_) {
        0 => {
            let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_848_ = leanh::lean_unsigned_to_nat(0);
            return v___x_848_;
        }
        1 => {
            let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_849_ = leanh::lean_unsigned_to_nat(1);
            return v___x_849_;
        }
        _ => {
            let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_850_ = leanh::lean_unsigned_to_nat(2);
            return v___x_850_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorIdx___boxed(
    mut v_x_851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_852_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorIdx(v_x_851_);
    leanh::lean_dec_ref(v_x_851_);
    return v_res_852_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(
    mut v_t_853_: *mut leanh::LeanObject,
    mut v_k_854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_853_) == 2 {
        let mut v_c_855_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_856_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_858_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_c_855_ = leanh::lean_ctor_get(v_t_853_, 0);
        leanh::lean_inc_ref(v_c_855_);
        v_val_856_ = leanh::lean_ctor_get(v_t_853_, 1);
        leanh::lean_inc(v_val_856_);
        v_x_857_ = leanh::lean_ctor_get(v_t_853_, 2);
        leanh::lean_inc(v_x_857_);
        v_n_858_ = leanh::lean_ctor_get(v_t_853_, 3);
        leanh::lean_inc(v_n_858_);
        leanh::lean_dec_ref_known(v_t_853_, 4);
        v___x_859_ = leanh::lean_apply_4(v_k_854_, v_c_855_, v_val_856_, v_x_857_, v_n_858_);
        return v___x_859_;
    } else {
        let mut v_e_860_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_lhs_861_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_862_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_e_860_ = leanh::lean_ctor_get(v_t_853_, 0);
        leanh::lean_inc_ref(v_e_860_);
        v_lhs_861_ = leanh::lean_ctor_get(v_t_853_, 1);
        leanh::lean_inc_ref(v_lhs_861_);
        v_rhs_862_ = leanh::lean_ctor_get(v_t_853_, 2);
        leanh::lean_inc_ref(v_rhs_862_);
        leanh::lean_dec_ref(v_t_853_);
        v___x_863_ = leanh::lean_apply_3(v_k_854_, v_e_860_, v_lhs_861_, v_rhs_862_);
        return v___x_863_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim(
    mut v_motive__2_864_: *mut leanh::LeanObject,
    mut v_ctorIdx_865_: *mut leanh::LeanObject,
    mut v_t_866_: *mut leanh::LeanObject,
    mut v_h_867_: *mut leanh::LeanObject,
    mut v_k_868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_869_ =
        l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(v_t_866_, v_k_868_);
    return v___x_869_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___boxed(
    mut v_motive__2_870_: *mut leanh::LeanObject,
    mut v_ctorIdx_871_: *mut leanh::LeanObject,
    mut v_t_872_: *mut leanh::LeanObject,
    mut v_h_873_: *mut leanh::LeanObject,
    mut v_k_874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_875_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim(
        v_motive__2_870_,
        v_ctorIdx_871_,
        v_t_872_,
        v_h_873_,
        v_k_874_,
    );
    leanh::lean_dec(v_ctorIdx_871_);
    return v_res_875_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_core_elim___redArg(
    mut v_t_876_: *mut leanh::LeanObject,
    mut v_core_877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_878_ =
        l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(v_t_876_, v_core_877_);
    return v___x_878_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_core_elim(
    mut v_motive__2_879_: *mut leanh::LeanObject,
    mut v_t_880_: *mut leanh::LeanObject,
    mut v_h_881_: *mut leanh::LeanObject,
    mut v_core_882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_883_ =
        l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(v_t_880_, v_core_882_);
    return v___x_883_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_notCore_elim___redArg(
    mut v_t_884_: *mut leanh::LeanObject,
    mut v_notCore_885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_886_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(
        v_t_884_,
        v_notCore_885_,
    );
    return v___x_886_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_notCore_elim(
    mut v_motive__2_887_: *mut leanh::LeanObject,
    mut v_t_888_: *mut leanh::LeanObject,
    mut v_h_889_: *mut leanh::LeanObject,
    mut v_notCore_890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_891_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(
        v_t_888_,
        v_notCore_890_,
    );
    return v___x_891_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_cancelDen_elim___redArg(
    mut v_t_892_: *mut leanh::LeanObject,
    mut v_cancelDen_893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_894_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(
        v_t_892_,
        v_cancelDen_893_,
    );
    return v___x_894_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_cancelDen_elim(
    mut v_motive__2_895_: *mut leanh::LeanObject,
    mut v_t_896_: *mut leanh::LeanObject,
    mut v_h_897_: *mut leanh::LeanObject,
    mut v_cancelDen_898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_899_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(
        v_t_896_,
        v_cancelDen_898_,
    );
    return v___x_899_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorIdx(
    mut v_x_900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_900_) {
        0 => {
            let mut v___x_901_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_901_ = leanh::lean_unsigned_to_nat(0);
            return v___x_901_;
        }
        1 => {
            let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_902_ = leanh::lean_unsigned_to_nat(1);
            return v___x_902_;
        }
        _ => {
            let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_903_ = leanh::lean_unsigned_to_nat(2);
            return v___x_903_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorIdx___boxed(
    mut v_x_904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_905_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorIdx(v_x_904_);
    leanh::lean_dec_ref(v_x_904_);
    return v_res_905_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(
    mut v_t_906_: *mut leanh::LeanObject,
    mut v_k_907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_906_) {
        0 => {
            let mut v_a_908_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_909_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_ra_910_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rb_911_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_908_ = leanh::lean_ctor_get(v_t_906_, 0);
            leanh::lean_inc_ref(v_a_908_);
            v_b_909_ = leanh::lean_ctor_get(v_t_906_, 1);
            leanh::lean_inc_ref(v_b_909_);
            v_ra_910_ = leanh::lean_ctor_get(v_t_906_, 2);
            leanh::lean_inc_ref(v_ra_910_);
            v_rb_911_ = leanh::lean_ctor_get(v_t_906_, 3);
            leanh::lean_inc_ref(v_rb_911_);
            leanh::lean_dec_ref_known(v_t_906_, 4);
            v___x_912_ =
                leanh::lean_apply_4(v_k_907_, v_a_908_, v_b_909_, v_ra_910_, v_rb_911_);
            return v___x_912_;
        }
        1 => {
            let mut v_c_913_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_c_913_ = leanh::lean_ctor_get(v_t_906_, 0);
            leanh::lean_inc_ref(v_c_913_);
            leanh::lean_dec_ref_known(v_t_906_, 1);
            v___x_914_ = leanh::lean_apply_1(v_k_907_, v_c_913_);
            return v___x_914_;
        }
        _ => {
            let mut v_c_915_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_916_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_918_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_c_915_ = leanh::lean_ctor_get(v_t_906_, 0);
            leanh::lean_inc_ref(v_c_915_);
            v_val_916_ = leanh::lean_ctor_get(v_t_906_, 1);
            leanh::lean_inc(v_val_916_);
            v_x_917_ = leanh::lean_ctor_get(v_t_906_, 2);
            leanh::lean_inc(v_x_917_);
            v_n_918_ = leanh::lean_ctor_get(v_t_906_, 3);
            leanh::lean_inc(v_n_918_);
            leanh::lean_dec_ref_known(v_t_906_, 4);
            v___x_919_ =
                leanh::lean_apply_4(v_k_907_, v_c_915_, v_val_916_, v_x_917_, v_n_918_);
            return v___x_919_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim(
    mut v_motive__2_920_: *mut leanh::LeanObject,
    mut v_ctorIdx_921_: *mut leanh::LeanObject,
    mut v_t_922_: *mut leanh::LeanObject,
    mut v_h_923_: *mut leanh::LeanObject,
    mut v_k_924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_925_ =
        l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_922_, v_k_924_);
    return v___x_925_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___boxed(
    mut v_motive__2_926_: *mut leanh::LeanObject,
    mut v_ctorIdx_927_: *mut leanh::LeanObject,
    mut v_t_928_: *mut leanh::LeanObject,
    mut v_h_929_: *mut leanh::LeanObject,
    mut v_k_930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_931_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim(
        v_motive__2_926_,
        v_ctorIdx_927_,
        v_t_928_,
        v_h_929_,
        v_k_930_,
    );
    leanh::lean_dec(v_ctorIdx_927_);
    return v_res_931_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_core_elim___redArg(
    mut v_t_932_: *mut leanh::LeanObject,
    mut v_core_933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_934_ =
        l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_932_, v_core_933_);
    return v___x_934_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_core_elim(
    mut v_motive__2_935_: *mut leanh::LeanObject,
    mut v_t_936_: *mut leanh::LeanObject,
    mut v_h_937_: *mut leanh::LeanObject,
    mut v_core_938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_939_ =
        l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_936_, v_core_938_);
    return v___x_939_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_symm_elim___redArg(
    mut v_t_940_: *mut leanh::LeanObject,
    mut v_symm_941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_942_ =
        l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_940_, v_symm_941_);
    return v___x_942_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_symm_elim(
    mut v_motive__2_943_: *mut leanh::LeanObject,
    mut v_t_944_: *mut leanh::LeanObject,
    mut v_h_945_: *mut leanh::LeanObject,
    mut v_symm_946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_947_ =
        l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_944_, v_symm_946_);
    return v___x_947_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_cancelDen_elim___redArg(
    mut v_t_948_: *mut leanh::LeanObject,
    mut v_cancelDen_949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_950_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(
        v_t_948_,
        v_cancelDen_949_,
    );
    return v___x_950_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_cancelDen_elim(
    mut v_motive__2_951_: *mut leanh::LeanObject,
    mut v_t_952_: *mut leanh::LeanObject,
    mut v_h_953_: *mut leanh::LeanObject,
    mut v_cancelDen_954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_955_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(
        v_t_952_,
        v_cancelDen_954_,
    );
    return v___x_955_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorIdx(
    mut v_x_956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_956_) == 0 {
        let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_957_ = leanh::lean_unsigned_to_nat(0);
        return v___x_957_;
    } else {
        let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_958_ = leanh::lean_unsigned_to_nat(1);
        return v___x_958_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorIdx___boxed(
    mut v_x_959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_960_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorIdx(v_x_959_);
    leanh::lean_dec_ref(v_x_959_);
    return v_res_960_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(
    mut v_t_961_: *mut leanh::LeanObject,
    mut v_k_962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_961_) == 0 {
        let mut v_a_963_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_b_964_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ra_965_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_rb_966_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_963_ = leanh::lean_ctor_get(v_t_961_, 0);
        leanh::lean_inc_ref(v_a_963_);
        v_b_964_ = leanh::lean_ctor_get(v_t_961_, 1);
        leanh::lean_inc_ref(v_b_964_);
        v_ra_965_ = leanh::lean_ctor_get(v_t_961_, 2);
        leanh::lean_inc_ref(v_ra_965_);
        v_rb_966_ = leanh::lean_ctor_get(v_t_961_, 3);
        leanh::lean_inc_ref(v_rb_966_);
        leanh::lean_dec_ref_known(v_t_961_, 4);
        v___x_967_ = leanh::lean_apply_4(v_k_962_, v_a_963_, v_b_964_, v_ra_965_, v_rb_966_);
        return v___x_967_;
    } else {
        let mut v_c_968_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_969_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_971_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_c_968_ = leanh::lean_ctor_get(v_t_961_, 0);
        leanh::lean_inc_ref(v_c_968_);
        v_val_969_ = leanh::lean_ctor_get(v_t_961_, 1);
        leanh::lean_inc(v_val_969_);
        v_x_970_ = leanh::lean_ctor_get(v_t_961_, 2);
        leanh::lean_inc(v_x_970_);
        v_n_971_ = leanh::lean_ctor_get(v_t_961_, 3);
        leanh::lean_inc(v_n_971_);
        leanh::lean_dec_ref_known(v_t_961_, 4);
        v___x_972_ = leanh::lean_apply_4(v_k_962_, v_c_968_, v_val_969_, v_x_970_, v_n_971_);
        return v___x_972_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim(
    mut v_motive__2_973_: *mut leanh::LeanObject,
    mut v_ctorIdx_974_: *mut leanh::LeanObject,
    mut v_t_975_: *mut leanh::LeanObject,
    mut v_h_976_: *mut leanh::LeanObject,
    mut v_k_977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_978_ =
        l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(v_t_975_, v_k_977_);
    return v___x_978_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___boxed(
    mut v_motive__2_979_: *mut leanh::LeanObject,
    mut v_ctorIdx_980_: *mut leanh::LeanObject,
    mut v_t_981_: *mut leanh::LeanObject,
    mut v_h_982_: *mut leanh::LeanObject,
    mut v_k_983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_984_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim(
        v_motive__2_979_,
        v_ctorIdx_980_,
        v_t_981_,
        v_h_982_,
        v_k_983_,
    );
    leanh::lean_dec(v_ctorIdx_980_);
    return v_res_984_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_core_elim___redArg(
    mut v_t_985_: *mut leanh::LeanObject,
    mut v_core_986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_987_ =
        l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(v_t_985_, v_core_986_);
    return v___x_987_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_core_elim(
    mut v_motive__2_988_: *mut leanh::LeanObject,
    mut v_t_989_: *mut leanh::LeanObject,
    mut v_h_990_: *mut leanh::LeanObject,
    mut v_core_991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_992_ =
        l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(v_t_989_, v_core_991_);
    return v___x_992_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_cancelDen_elim___redArg(
    mut v_t_993_: *mut leanh::LeanObject,
    mut v_cancelDen_994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_995_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(
        v_t_993_,
        v_cancelDen_994_,
    );
    return v___x_995_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_cancelDen_elim(
    mut v_motive__2_996_: *mut leanh::LeanObject,
    mut v_t_997_: *mut leanh::LeanObject,
    mut v_h_998_: *mut leanh::LeanObject,
    mut v_cancelDen_999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1000_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(
        v_t_997_,
        v_cancelDen_999_,
    );
    return v___x_1000_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorIdx(
    mut v_x_1001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1001_) {
        0 => {
            let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1002_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1002_;
        }
        1 => {
            let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1003_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1003_;
        }
        2 => {
            let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1004_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1004_;
        }
        3 => {
            let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1005_ = leanh::lean_unsigned_to_nat(3);
            return v___x_1005_;
        }
        4 => {
            let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1006_ = leanh::lean_unsigned_to_nat(4);
            return v___x_1006_;
        }
        _ => {
            let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1007_ = leanh::lean_unsigned_to_nat(5);
            return v___x_1007_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorIdx___boxed(
    mut v_x_1008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1009_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorIdx(v_x_1008_);
    leanh::lean_dec_ref(v_x_1008_);
    return v_res_1009_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(
    mut v_t_1010_: *mut leanh::LeanObject,
    mut v_k_1011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_1010_) {
        0 => {
            let mut v_a_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_1012_ = leanh::lean_ctor_get(v_t_1010_, 0);
            leanh::lean_inc_ref(v_a_1012_);
            v_b_1013_ = leanh::lean_ctor_get(v_t_1010_, 1);
            leanh::lean_inc_ref(v_b_1013_);
            v_lhs_1014_ = leanh::lean_ctor_get(v_t_1010_, 2);
            leanh::lean_inc(v_lhs_1014_);
            v_rhs_1015_ = leanh::lean_ctor_get(v_t_1010_, 3);
            leanh::lean_inc(v_rhs_1015_);
            leanh::lean_dec_ref_known(v_t_1010_, 4);
            v___x_1016_ = leanh::lean_apply_4(
                v_k_1011_,
                v_a_1012_,
                v_b_1013_,
                v_lhs_1014_,
                v_rhs_1015_,
            );
            return v___x_1016_;
        }
        1 => {
            let mut v_a_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_ra_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rb_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_x27_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_1017_ = leanh::lean_ctor_get(v_t_1010_, 0);
            leanh::lean_inc_ref(v_a_1017_);
            v_b_1018_ = leanh::lean_ctor_get(v_t_1010_, 1);
            leanh::lean_inc_ref(v_b_1018_);
            v_ra_1019_ = leanh::lean_ctor_get(v_t_1010_, 2);
            leanh::lean_inc_ref(v_ra_1019_);
            v_rb_1020_ = leanh::lean_ctor_get(v_t_1010_, 3);
            leanh::lean_inc_ref(v_rb_1020_);
            v_p_1021_ = leanh::lean_ctor_get(v_t_1010_, 4);
            leanh::lean_inc_ref(v_p_1021_);
            v_lhs_x27_1022_ = leanh::lean_ctor_get(v_t_1010_, 5);
            leanh::lean_inc(v_lhs_x27_1022_);
            leanh::lean_dec_ref_known(v_t_1010_, 6);
            v___x_1023_ = leanh::lean_apply_6(
                v_k_1011_,
                v_a_1017_,
                v_b_1018_,
                v_ra_1019_,
                v_rb_1020_,
                v_p_1021_,
                v_lhs_x27_1022_,
            );
            return v___x_1023_;
        }
        2 => {
            let mut v_a_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_natStructId_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_1024_ = leanh::lean_ctor_get(v_t_1010_, 0);
            leanh::lean_inc_ref(v_a_1024_);
            v_b_1025_ = leanh::lean_ctor_get(v_t_1010_, 1);
            leanh::lean_inc_ref(v_b_1025_);
            v_natStructId_1026_ = leanh::lean_ctor_get(v_t_1010_, 2);
            leanh::lean_inc(v_natStructId_1026_);
            v_lhs_1027_ = leanh::lean_ctor_get(v_t_1010_, 3);
            leanh::lean_inc(v_lhs_1027_);
            v_rhs_1028_ = leanh::lean_ctor_get(v_t_1010_, 4);
            leanh::lean_inc(v_rhs_1028_);
            leanh::lean_dec_ref_known(v_t_1010_, 5);
            v___x_1029_ = leanh::lean_apply_5(
                v_k_1011_,
                v_a_1024_,
                v_b_1025_,
                v_natStructId_1026_,
                v_lhs_1027_,
                v_rhs_1028_,
            );
            return v___x_1029_;
        }
        3 => {
            let mut v_c_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_c_1030_ = leanh::lean_ctor_get(v_t_1010_, 0);
            leanh::lean_inc_ref(v_c_1030_);
            leanh::lean_dec_ref_known(v_t_1010_, 1);
            v___x_1031_ = leanh::lean_apply_1(v_k_1011_, v_c_1030_);
            return v___x_1031_;
        }
        4 => {
            let mut v_k_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_k_1032_ = leanh::lean_ctor_get(v_t_1010_, 0);
            leanh::lean_inc(v_k_1032_);
            v_c_1033_ = leanh::lean_ctor_get(v_t_1010_, 1);
            leanh::lean_inc_ref(v_c_1033_);
            leanh::lean_dec_ref_known(v_t_1010_, 2);
            v___x_1034_ = leanh::lean_apply_2(v_k_1011_, v_k_1032_, v_c_1033_);
            return v___x_1034_;
        }
        _ => {
            let mut v_x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_x_1035_ = leanh::lean_ctor_get(v_t_1010_, 0);
            leanh::lean_inc(v_x_1035_);
            v_c_u2081_1036_ = leanh::lean_ctor_get(v_t_1010_, 1);
            leanh::lean_inc_ref(v_c_u2081_1036_);
            v_c_u2082_1037_ = leanh::lean_ctor_get(v_t_1010_, 2);
            leanh::lean_inc_ref(v_c_u2082_1037_);
            leanh::lean_dec_ref_known(v_t_1010_, 3);
            v___x_1038_ =
                leanh::lean_apply_3(v_k_1011_, v_x_1035_, v_c_u2081_1036_, v_c_u2082_1037_);
            return v___x_1038_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim(
    mut v_motive__2_1039_: *mut leanh::LeanObject,
    mut v_ctorIdx_1040_: *mut leanh::LeanObject,
    mut v_t_1041_: *mut leanh::LeanObject,
    mut v_h_1042_: *mut leanh::LeanObject,
    mut v_k_1043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1044_ =
        l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_1041_, v_k_1043_);
    return v___x_1044_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___boxed(
    mut v_motive__2_1045_: *mut leanh::LeanObject,
    mut v_ctorIdx_1046_: *mut leanh::LeanObject,
    mut v_t_1047_: *mut leanh::LeanObject,
    mut v_h_1048_: *mut leanh::LeanObject,
    mut v_k_1049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1050_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim(
        v_motive__2_1045_,
        v_ctorIdx_1046_,
        v_t_1047_,
        v_h_1048_,
        v_k_1049_,
    );
    leanh::lean_dec(v_ctorIdx_1046_);
    return v_res_1050_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_core_elim___redArg(
    mut v_t_1051_: *mut leanh::LeanObject,
    mut v_core_1052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1053_ =
        l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_1051_, v_core_1052_);
    return v___x_1053_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_core_elim(
    mut v_motive__2_1054_: *mut leanh::LeanObject,
    mut v_t_1055_: *mut leanh::LeanObject,
    mut v_h_1056_: *mut leanh::LeanObject,
    mut v_core_1057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1058_ =
        l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_1055_, v_core_1057_);
    return v___x_1058_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreCommRing_elim___redArg(
    mut v_t_1059_: *mut leanh::LeanObject,
    mut v_coreCommRing_1060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1061_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(
        v_t_1059_,
        v_coreCommRing_1060_,
    );
    return v___x_1061_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreCommRing_elim(
    mut v_motive__2_1062_: *mut leanh::LeanObject,
    mut v_t_1063_: *mut leanh::LeanObject,
    mut v_h_1064_: *mut leanh::LeanObject,
    mut v_coreCommRing_1065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1066_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(
        v_t_1063_,
        v_coreCommRing_1065_,
    );
    return v___x_1066_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreOfNat_elim___redArg(
    mut v_t_1067_: *mut leanh::LeanObject,
    mut v_coreOfNat_1068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1069_ =
        l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_1067_, v_coreOfNat_1068_);
    return v___x_1069_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreOfNat_elim(
    mut v_motive__2_1070_: *mut leanh::LeanObject,
    mut v_t_1071_: *mut leanh::LeanObject,
    mut v_h_1072_: *mut leanh::LeanObject,
    mut v_coreOfNat_1073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1074_ =
        l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_1071_, v_coreOfNat_1073_);
    return v___x_1074_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_neg_elim___redArg(
    mut v_t_1075_: *mut leanh::LeanObject,
    mut v_neg_1076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1077_ =
        l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_1075_, v_neg_1076_);
    return v___x_1077_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_neg_elim(
    mut v_motive__2_1078_: *mut leanh::LeanObject,
    mut v_t_1079_: *mut leanh::LeanObject,
    mut v_h_1080_: *mut leanh::LeanObject,
    mut v_neg_1081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1082_ =
        l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_1079_, v_neg_1081_);
    return v___x_1082_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coeff_elim___redArg(
    mut v_t_1083_: *mut leanh::LeanObject,
    mut v_coeff_1084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1085_ =
        l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_1083_, v_coeff_1084_);
    return v___x_1085_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coeff_elim(
    mut v_motive__2_1086_: *mut leanh::LeanObject,
    mut v_t_1087_: *mut leanh::LeanObject,
    mut v_h_1088_: *mut leanh::LeanObject,
    mut v_coeff_1089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1090_ =
        l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_1087_, v_coeff_1089_);
    return v___x_1090_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_subst_elim___redArg(
    mut v_t_1091_: *mut leanh::LeanObject,
    mut v_subst_1092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1093_ =
        l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_1091_, v_subst_1092_);
    return v___x_1093_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_subst_elim(
    mut v_motive__2_1094_: *mut leanh::LeanObject,
    mut v_t_1095_: *mut leanh::LeanObject,
    mut v_h_1096_: *mut leanh::LeanObject,
    mut v_subst_1097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1098_ =
        l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_1095_, v_subst_1097_);
    return v___x_1098_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorIdx(
    mut v_x_1099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1099_) {
        0 => {
            let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1100_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1100_;
        }
        1 => {
            let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1101_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1101_;
        }
        2 => {
            let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1102_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1102_;
        }
        3 => {
            let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1103_ = leanh::lean_unsigned_to_nat(3);
            return v___x_1103_;
        }
        4 => {
            let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1104_ = leanh::lean_unsigned_to_nat(4);
            return v___x_1104_;
        }
        5 => {
            let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1105_ = leanh::lean_unsigned_to_nat(5);
            return v___x_1105_;
        }
        6 => {
            let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1106_ = leanh::lean_unsigned_to_nat(6);
            return v___x_1106_;
        }
        7 => {
            let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1107_ = leanh::lean_unsigned_to_nat(7);
            return v___x_1107_;
        }
        8 => {
            let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1108_ = leanh::lean_unsigned_to_nat(8);
            return v___x_1108_;
        }
        9 => {
            let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1109_ = leanh::lean_unsigned_to_nat(9);
            return v___x_1109_;
        }
        10 => {
            let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1110_ = leanh::lean_unsigned_to_nat(10);
            return v___x_1110_;
        }
        11 => {
            let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1111_ = leanh::lean_unsigned_to_nat(11);
            return v___x_1111_;
        }
        12 => {
            let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1112_ = leanh::lean_unsigned_to_nat(12);
            return v___x_1112_;
        }
        _ => {
            let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1113_ = leanh::lean_unsigned_to_nat(13);
            return v___x_1113_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorIdx___boxed(
    mut v_x_1114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1115_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorIdx(v_x_1114_);
    leanh::lean_dec(v_x_1114_);
    return v_res_1115_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(
    mut v_t_1116_: *mut leanh::LeanObject,
    mut v_k_1117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_1116_) {
        0 => {
            let mut v_e_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_e_1118_ = leanh::lean_ctor_get(v_t_1116_, 0);
            leanh::lean_inc_ref(v_e_1118_);
            v_lhs_1119_ = leanh::lean_ctor_get(v_t_1116_, 1);
            leanh::lean_inc(v_lhs_1119_);
            v_rhs_1120_ = leanh::lean_ctor_get(v_t_1116_, 2);
            leanh::lean_inc(v_rhs_1120_);
            leanh::lean_dec_ref_known(v_t_1116_, 3);
            v___x_1121_ =
                leanh::lean_apply_3(v_k_1117_, v_e_1118_, v_lhs_1119_, v_rhs_1120_);
            return v___x_1121_;
        }
        1 => {
            let mut v_e_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_e_1122_ = leanh::lean_ctor_get(v_t_1116_, 0);
            leanh::lean_inc_ref(v_e_1122_);
            v_lhs_1123_ = leanh::lean_ctor_get(v_t_1116_, 1);
            leanh::lean_inc(v_lhs_1123_);
            v_rhs_1124_ = leanh::lean_ctor_get(v_t_1116_, 2);
            leanh::lean_inc(v_rhs_1124_);
            leanh::lean_dec_ref_known(v_t_1116_, 3);
            v___x_1125_ =
                leanh::lean_apply_3(v_k_1117_, v_e_1122_, v_lhs_1123_, v_rhs_1124_);
            return v___x_1125_;
        }
        3 => {
            let mut v_e_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_natStructId_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_e_1126_ = leanh::lean_ctor_get(v_t_1116_, 0);
            leanh::lean_inc_ref(v_e_1126_);
            v_natStructId_1127_ = leanh::lean_ctor_get(v_t_1116_, 1);
            leanh::lean_inc(v_natStructId_1127_);
            v_lhs_1128_ = leanh::lean_ctor_get(v_t_1116_, 2);
            leanh::lean_inc(v_lhs_1128_);
            v_rhs_1129_ = leanh::lean_ctor_get(v_t_1116_, 3);
            leanh::lean_inc(v_rhs_1129_);
            leanh::lean_dec_ref_known(v_t_1116_, 4);
            v___x_1130_ = leanh::lean_apply_4(
                v_k_1117_,
                v_e_1126_,
                v_natStructId_1127_,
                v_lhs_1128_,
                v_rhs_1129_,
            );
            return v___x_1130_;
        }
        4 => {
            let mut v_e_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_natStructId_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_e_1131_ = leanh::lean_ctor_get(v_t_1116_, 0);
            leanh::lean_inc_ref(v_e_1131_);
            v_natStructId_1132_ = leanh::lean_ctor_get(v_t_1116_, 1);
            leanh::lean_inc(v_natStructId_1132_);
            v_lhs_1133_ = leanh::lean_ctor_get(v_t_1116_, 2);
            leanh::lean_inc(v_lhs_1133_);
            v_rhs_1134_ = leanh::lean_ctor_get(v_t_1116_, 3);
            leanh::lean_inc(v_rhs_1134_);
            leanh::lean_dec_ref_known(v_t_1116_, 4);
            v___x_1135_ = leanh::lean_apply_4(
                v_k_1117_,
                v_e_1131_,
                v_natStructId_1132_,
                v_lhs_1133_,
                v_rhs_1134_,
            );
            return v___x_1135_;
        }
        5 => {
            let mut v_c_u2081_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_c_u2081_1136_ = leanh::lean_ctor_get(v_t_1116_, 0);
            leanh::lean_inc_ref(v_c_u2081_1136_);
            v_c_u2082_1137_ = leanh::lean_ctor_get(v_t_1116_, 1);
            leanh::lean_inc_ref(v_c_u2082_1137_);
            leanh::lean_dec_ref_known(v_t_1116_, 2);
            v___x_1138_ = leanh::lean_apply_2(v_k_1117_, v_c_u2081_1136_, v_c_u2082_1137_);
            return v___x_1138_;
        }
        7 => {
            let mut v_h_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_h_1139_ = leanh::lean_ctor_get(v_t_1116_, 0);
            leanh::lean_inc(v_h_1139_);
            leanh::lean_dec_ref_known(v_t_1116_, 1);
            v___x_1140_ = leanh::lean_apply_1(v_k_1117_, v_h_1139_);
            return v___x_1140_;
        }
        8 => {
            let mut v_c_u2081_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_decVar_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_h_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_decVars_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_c_u2081_1141_ = leanh::lean_ctor_get(v_t_1116_, 0);
            leanh::lean_inc_ref(v_c_u2081_1141_);
            v_decVar_1142_ = leanh::lean_ctor_get(v_t_1116_, 1);
            leanh::lean_inc(v_decVar_1142_);
            v_h_1143_ = leanh::lean_ctor_get(v_t_1116_, 2);
            leanh::lean_inc_ref(v_h_1143_);
            v_decVars_1144_ = leanh::lean_ctor_get(v_t_1116_, 3);
            leanh::lean_inc_ref(v_decVars_1144_);
            leanh::lean_dec_ref_known(v_t_1116_, 4);
            v___x_1145_ = leanh::lean_apply_4(
                v_k_1117_,
                v_c_u2081_1141_,
                v_decVar_1142_,
                v_h_1143_,
                v_decVars_1144_,
            );
            return v___x_1145_;
        }
        9 => {
            return v_k_1117_;
        }
        10 => {
            let mut v_a_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_la_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lb_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_1146_ = leanh::lean_ctor_get(v_t_1116_, 0);
            leanh::lean_inc_ref(v_a_1146_);
            v_b_1147_ = leanh::lean_ctor_get(v_t_1116_, 1);
            leanh::lean_inc_ref(v_b_1147_);
            v_la_1148_ = leanh::lean_ctor_get(v_t_1116_, 2);
            leanh::lean_inc(v_la_1148_);
            v_lb_1149_ = leanh::lean_ctor_get(v_t_1116_, 3);
            leanh::lean_inc(v_lb_1149_);
            leanh::lean_dec_ref_known(v_t_1116_, 4);
            v___x_1150_ =
                leanh::lean_apply_4(v_k_1117_, v_a_1146_, v_b_1147_, v_la_1148_, v_lb_1149_);
            return v___x_1150_;
        }
        11 => {
            let mut v_a_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_natStructId_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_la_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lb_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_1151_ = leanh::lean_ctor_get(v_t_1116_, 0);
            leanh::lean_inc_ref(v_a_1151_);
            v_b_1152_ = leanh::lean_ctor_get(v_t_1116_, 1);
            leanh::lean_inc_ref(v_b_1152_);
            v_natStructId_1153_ = leanh::lean_ctor_get(v_t_1116_, 2);
            leanh::lean_inc(v_natStructId_1153_);
            v_la_1154_ = leanh::lean_ctor_get(v_t_1116_, 3);
            leanh::lean_inc(v_la_1154_);
            v_lb_1155_ = leanh::lean_ctor_get(v_t_1116_, 4);
            leanh::lean_inc(v_lb_1155_);
            leanh::lean_dec_ref_known(v_t_1116_, 5);
            v___x_1156_ = leanh::lean_apply_5(
                v_k_1117_,
                v_a_1151_,
                v_b_1152_,
                v_natStructId_1153_,
                v_la_1154_,
                v_lb_1155_,
            );
            return v___x_1156_;
        }
        13 => {
            let mut v_x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_x_1157_ = leanh::lean_ctor_get(v_t_1116_, 0);
            leanh::lean_inc(v_x_1157_);
            v_c_u2081_1158_ = leanh::lean_ctor_get(v_t_1116_, 1);
            leanh::lean_inc_ref(v_c_u2081_1158_);
            v_c_u2082_1159_ = leanh::lean_ctor_get(v_t_1116_, 2);
            leanh::lean_inc_ref(v_c_u2082_1159_);
            leanh::lean_dec_ref_known(v_t_1116_, 3);
            v___x_1160_ =
                leanh::lean_apply_3(v_k_1117_, v_x_1157_, v_c_u2081_1158_, v_c_u2082_1159_);
            return v___x_1160_;
        }
        _ => {
            let mut v_c_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_c_1161_ = leanh::lean_ctor_get(v_t_1116_, 0);
            leanh::lean_inc_ref(v_c_1161_);
            v_lhs_1162_ = leanh::lean_ctor_get(v_t_1116_, 1);
            leanh::lean_inc(v_lhs_1162_);
            leanh::lean_dec(v_t_1116_);
            v___x_1163_ = leanh::lean_apply_2(v_k_1117_, v_c_1161_, v_lhs_1162_);
            return v___x_1163_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim(
    mut v_motive__4_1164_: *mut leanh::LeanObject,
    mut v_ctorIdx_1165_: *mut leanh::LeanObject,
    mut v_t_1166_: *mut leanh::LeanObject,
    mut v_h_1167_: *mut leanh::LeanObject,
    mut v_k_1168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1169_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1166_, v_k_1168_);
    return v___x_1169_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___boxed(
    mut v_motive__4_1170_: *mut leanh::LeanObject,
    mut v_ctorIdx_1171_: *mut leanh::LeanObject,
    mut v_t_1172_: *mut leanh::LeanObject,
    mut v_h_1173_: *mut leanh::LeanObject,
    mut v_k_1174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1175_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim(
        v_motive__4_1170_,
        v_ctorIdx_1171_,
        v_t_1172_,
        v_h_1173_,
        v_k_1174_,
    );
    leanh::lean_dec(v_ctorIdx_1171_);
    return v_res_1175_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_core_elim___redArg(
    mut v_t_1176_: *mut leanh::LeanObject,
    mut v_core_1177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1178_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1176_, v_core_1177_);
    return v___x_1178_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_core_elim(
    mut v_motive__4_1179_: *mut leanh::LeanObject,
    mut v_t_1180_: *mut leanh::LeanObject,
    mut v_h_1181_: *mut leanh::LeanObject,
    mut v_core_1182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1183_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1180_, v_core_1182_);
    return v___x_1183_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCore_elim___redArg(
    mut v_t_1184_: *mut leanh::LeanObject,
    mut v_notCore_1185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1186_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1184_, v_notCore_1185_);
    return v___x_1186_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCore_elim(
    mut v_motive__4_1187_: *mut leanh::LeanObject,
    mut v_t_1188_: *mut leanh::LeanObject,
    mut v_h_1189_: *mut leanh::LeanObject,
    mut v_notCore_1190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1191_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1188_, v_notCore_1190_);
    return v___x_1191_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ring_elim___redArg(
    mut v_t_1192_: *mut leanh::LeanObject,
    mut v_ring_1193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1194_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1192_, v_ring_1193_);
    return v___x_1194_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ring_elim(
    mut v_motive__4_1195_: *mut leanh::LeanObject,
    mut v_t_1196_: *mut leanh::LeanObject,
    mut v_h_1197_: *mut leanh::LeanObject,
    mut v_ring_1198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1199_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1196_, v_ring_1198_);
    return v___x_1199_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_coreOfNat_elim___redArg(
    mut v_t_1200_: *mut leanh::LeanObject,
    mut v_coreOfNat_1201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1202_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(
        v_t_1200_,
        v_coreOfNat_1201_,
    );
    return v___x_1202_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_coreOfNat_elim(
    mut v_motive__4_1203_: *mut leanh::LeanObject,
    mut v_t_1204_: *mut leanh::LeanObject,
    mut v_h_1205_: *mut leanh::LeanObject,
    mut v_coreOfNat_1206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1207_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(
        v_t_1204_,
        v_coreOfNat_1206_,
    );
    return v___x_1207_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCoreOfNat_elim___redArg(
    mut v_t_1208_: *mut leanh::LeanObject,
    mut v_notCoreOfNat_1209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1210_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(
        v_t_1208_,
        v_notCoreOfNat_1209_,
    );
    return v___x_1210_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCoreOfNat_elim(
    mut v_motive__4_1211_: *mut leanh::LeanObject,
    mut v_t_1212_: *mut leanh::LeanObject,
    mut v_h_1213_: *mut leanh::LeanObject,
    mut v_notCoreOfNat_1214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1215_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(
        v_t_1212_,
        v_notCoreOfNat_1214_,
    );
    return v___x_1215_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_combine_elim___redArg(
    mut v_t_1216_: *mut leanh::LeanObject,
    mut v_combine_1217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1218_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1216_, v_combine_1217_);
    return v___x_1218_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_combine_elim(
    mut v_motive__4_1219_: *mut leanh::LeanObject,
    mut v_t_1220_: *mut leanh::LeanObject,
    mut v_h_1221_: *mut leanh::LeanObject,
    mut v_combine_1222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1223_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1220_, v_combine_1222_);
    return v___x_1223_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_norm_elim___redArg(
    mut v_t_1224_: *mut leanh::LeanObject,
    mut v_norm_1225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1226_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1224_, v_norm_1225_);
    return v___x_1226_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_norm_elim(
    mut v_motive__4_1227_: *mut leanh::LeanObject,
    mut v_t_1228_: *mut leanh::LeanObject,
    mut v_h_1229_: *mut leanh::LeanObject,
    mut v_norm_1230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1231_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1228_, v_norm_1230_);
    return v___x_1231_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_dec_elim___redArg(
    mut v_t_1232_: *mut leanh::LeanObject,
    mut v_dec_1233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1234_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1232_, v_dec_1233_);
    return v___x_1234_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_dec_elim(
    mut v_motive__4_1235_: *mut leanh::LeanObject,
    mut v_t_1236_: *mut leanh::LeanObject,
    mut v_h_1237_: *mut leanh::LeanObject,
    mut v_dec_1238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1239_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1236_, v_dec_1238_);
    return v___x_1239_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofDiseqSplit_elim___redArg(
    mut v_t_1240_: *mut leanh::LeanObject,
    mut v_ofDiseqSplit_1241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1242_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(
        v_t_1240_,
        v_ofDiseqSplit_1241_,
    );
    return v___x_1242_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofDiseqSplit_elim(
    mut v_motive__4_1243_: *mut leanh::LeanObject,
    mut v_t_1244_: *mut leanh::LeanObject,
    mut v_h_1245_: *mut leanh::LeanObject,
    mut v_ofDiseqSplit_1246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1247_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(
        v_t_1244_,
        v_ofDiseqSplit_1246_,
    );
    return v___x_1247_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_oneGtZero_elim___redArg(
    mut v_t_1248_: *mut leanh::LeanObject,
    mut v_oneGtZero_1249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1250_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(
        v_t_1248_,
        v_oneGtZero_1249_,
    );
    return v___x_1250_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_oneGtZero_elim(
    mut v_motive__4_1251_: *mut leanh::LeanObject,
    mut v_t_1252_: *mut leanh::LeanObject,
    mut v_h_1253_: *mut leanh::LeanObject,
    mut v_oneGtZero_1254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1255_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(
        v_t_1252_,
        v_oneGtZero_1254_,
    );
    return v___x_1255_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEq_elim___redArg(
    mut v_t_1256_: *mut leanh::LeanObject,
    mut v_ofEq_1257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1258_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1256_, v_ofEq_1257_);
    return v___x_1258_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEq_elim(
    mut v_motive__4_1259_: *mut leanh::LeanObject,
    mut v_t_1260_: *mut leanh::LeanObject,
    mut v_h_1261_: *mut leanh::LeanObject,
    mut v_ofEq_1262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1263_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1260_, v_ofEq_1262_);
    return v___x_1263_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEqOfNat_elim___redArg(
    mut v_t_1264_: *mut leanh::LeanObject,
    mut v_ofEqOfNat_1265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1266_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(
        v_t_1264_,
        v_ofEqOfNat_1265_,
    );
    return v___x_1266_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEqOfNat_elim(
    mut v_motive__4_1267_: *mut leanh::LeanObject,
    mut v_t_1268_: *mut leanh::LeanObject,
    mut v_h_1269_: *mut leanh::LeanObject,
    mut v_ofEqOfNat_1270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1271_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(
        v_t_1268_,
        v_ofEqOfNat_1270_,
    );
    return v___x_1271_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ringEq_elim___redArg(
    mut v_t_1272_: *mut leanh::LeanObject,
    mut v_ringEq_1273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1274_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1272_, v_ringEq_1273_);
    return v___x_1274_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ringEq_elim(
    mut v_motive__4_1275_: *mut leanh::LeanObject,
    mut v_t_1276_: *mut leanh::LeanObject,
    mut v_h_1277_: *mut leanh::LeanObject,
    mut v_ringEq_1278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1279_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1276_, v_ringEq_1278_);
    return v___x_1279_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_subst_elim___redArg(
    mut v_t_1280_: *mut leanh::LeanObject,
    mut v_subst_1281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1282_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1280_, v_subst_1281_);
    return v___x_1282_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_subst_elim(
    mut v_motive__4_1283_: *mut leanh::LeanObject,
    mut v_t_1284_: *mut leanh::LeanObject,
    mut v_h_1285_: *mut leanh::LeanObject,
    mut v_subst_1286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1287_ =
        l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_1284_, v_subst_1286_);
    return v___x_1287_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorIdx(
    mut v_x_1288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1288_) {
        0 => {
            let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1289_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1289_;
        }
        1 => {
            let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1290_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1290_;
        }
        2 => {
            let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1291_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1291_;
        }
        3 => {
            let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1292_ = leanh::lean_unsigned_to_nat(3);
            return v___x_1292_;
        }
        4 => {
            let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1293_ = leanh::lean_unsigned_to_nat(4);
            return v___x_1293_;
        }
        5 => {
            let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1294_ = leanh::lean_unsigned_to_nat(5);
            return v___x_1294_;
        }
        _ => {
            let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1295_ = leanh::lean_unsigned_to_nat(6);
            return v___x_1295_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorIdx___boxed(
    mut v_x_1296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1297_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorIdx(v_x_1296_);
    leanh::lean_dec(v_x_1296_);
    return v_res_1297_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(
    mut v_t_1298_: *mut leanh::LeanObject,
    mut v_k_1299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_1298_) {
        0 => {
            let mut v_a_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_1300_ = leanh::lean_ctor_get(v_t_1298_, 0);
            leanh::lean_inc_ref(v_a_1300_);
            v_b_1301_ = leanh::lean_ctor_get(v_t_1298_, 1);
            leanh::lean_inc_ref(v_b_1301_);
            v_lhs_1302_ = leanh::lean_ctor_get(v_t_1298_, 2);
            leanh::lean_inc(v_lhs_1302_);
            v_rhs_1303_ = leanh::lean_ctor_get(v_t_1298_, 3);
            leanh::lean_inc(v_rhs_1303_);
            leanh::lean_dec_ref_known(v_t_1298_, 4);
            v___x_1304_ = leanh::lean_apply_4(
                v_k_1299_,
                v_a_1300_,
                v_b_1301_,
                v_lhs_1302_,
                v_rhs_1303_,
            );
            return v___x_1304_;
        }
        1 => {
            let mut v_c_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_c_1305_ = leanh::lean_ctor_get(v_t_1298_, 0);
            leanh::lean_inc_ref(v_c_1305_);
            v_lhs_1306_ = leanh::lean_ctor_get(v_t_1298_, 1);
            leanh::lean_inc(v_lhs_1306_);
            leanh::lean_dec_ref_known(v_t_1298_, 2);
            v___x_1307_ = leanh::lean_apply_2(v_k_1299_, v_c_1305_, v_lhs_1306_);
            return v___x_1307_;
        }
        2 => {
            let mut v_a_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_natStructId_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_1308_ = leanh::lean_ctor_get(v_t_1298_, 0);
            leanh::lean_inc_ref(v_a_1308_);
            v_b_1309_ = leanh::lean_ctor_get(v_t_1298_, 1);
            leanh::lean_inc_ref(v_b_1309_);
            v_natStructId_1310_ = leanh::lean_ctor_get(v_t_1298_, 2);
            leanh::lean_inc(v_natStructId_1310_);
            v_lhs_1311_ = leanh::lean_ctor_get(v_t_1298_, 3);
            leanh::lean_inc(v_lhs_1311_);
            v_rhs_1312_ = leanh::lean_ctor_get(v_t_1298_, 4);
            leanh::lean_inc(v_rhs_1312_);
            leanh::lean_dec_ref_known(v_t_1298_, 5);
            v___x_1313_ = leanh::lean_apply_5(
                v_k_1299_,
                v_a_1308_,
                v_b_1309_,
                v_natStructId_1310_,
                v_lhs_1311_,
                v_rhs_1312_,
            );
            return v___x_1313_;
        }
        3 => {
            let mut v_c_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_c_1314_ = leanh::lean_ctor_get(v_t_1298_, 0);
            leanh::lean_inc_ref(v_c_1314_);
            leanh::lean_dec_ref_known(v_t_1298_, 1);
            v___x_1315_ = leanh::lean_apply_1(v_k_1299_, v_c_1314_);
            return v___x_1315_;
        }
        4 => {
            let mut v_k_u2081_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_u2082_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_k_u2081_1316_ = leanh::lean_ctor_get(v_t_1298_, 0);
            leanh::lean_inc(v_k_u2081_1316_);
            v_k_u2082_1317_ = leanh::lean_ctor_get(v_t_1298_, 1);
            leanh::lean_inc(v_k_u2082_1317_);
            v_c_u2081_1318_ = leanh::lean_ctor_get(v_t_1298_, 2);
            leanh::lean_inc_ref(v_c_u2081_1318_);
            v_c_u2082_1319_ = leanh::lean_ctor_get(v_t_1298_, 3);
            leanh::lean_inc_ref(v_c_u2082_1319_);
            leanh::lean_dec_ref_known(v_t_1298_, 4);
            v___x_1320_ = leanh::lean_apply_4(
                v_k_1299_,
                v_k_u2081_1316_,
                v_k_u2082_1317_,
                v_c_u2081_1318_,
                v_c_u2082_1319_,
            );
            return v___x_1320_;
        }
        5 => {
            let mut v_k_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_k_1321_ = leanh::lean_ctor_get(v_t_1298_, 0);
            leanh::lean_inc(v_k_1321_);
            v_c_u2081_1322_ = leanh::lean_ctor_get(v_t_1298_, 1);
            leanh::lean_inc_ref(v_c_u2081_1322_);
            v_c_u2082_1323_ = leanh::lean_ctor_get(v_t_1298_, 2);
            leanh::lean_inc_ref(v_c_u2082_1323_);
            leanh::lean_dec_ref_known(v_t_1298_, 3);
            v___x_1324_ =
                leanh::lean_apply_3(v_k_1299_, v_k_1321_, v_c_u2081_1322_, v_c_u2082_1323_);
            return v___x_1324_;
        }
        _ => {
            return v_k_1299_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim(
    mut v_motive__6_1325_: *mut leanh::LeanObject,
    mut v_ctorIdx_1326_: *mut leanh::LeanObject,
    mut v_t_1327_: *mut leanh::LeanObject,
    mut v_h_1328_: *mut leanh::LeanObject,
    mut v_k_1329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1330_ =
        l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_1327_, v_k_1329_);
    return v___x_1330_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___boxed(
    mut v_motive__6_1331_: *mut leanh::LeanObject,
    mut v_ctorIdx_1332_: *mut leanh::LeanObject,
    mut v_t_1333_: *mut leanh::LeanObject,
    mut v_h_1334_: *mut leanh::LeanObject,
    mut v_k_1335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1336_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim(
        v_motive__6_1331_,
        v_ctorIdx_1332_,
        v_t_1333_,
        v_h_1334_,
        v_k_1335_,
    );
    leanh::lean_dec(v_ctorIdx_1332_);
    return v_res_1336_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_core_elim___redArg(
    mut v_t_1337_: *mut leanh::LeanObject,
    mut v_core_1338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1339_ =
        l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_1337_, v_core_1338_);
    return v___x_1339_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_core_elim(
    mut v_motive__6_1340_: *mut leanh::LeanObject,
    mut v_t_1341_: *mut leanh::LeanObject,
    mut v_h_1342_: *mut leanh::LeanObject,
    mut v_core_1343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1344_ =
        l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_1341_, v_core_1343_);
    return v___x_1344_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ring_elim___redArg(
    mut v_t_1345_: *mut leanh::LeanObject,
    mut v_ring_1346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1347_ =
        l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_1345_, v_ring_1346_);
    return v___x_1347_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ring_elim(
    mut v_motive__6_1348_: *mut leanh::LeanObject,
    mut v_t_1349_: *mut leanh::LeanObject,
    mut v_h_1350_: *mut leanh::LeanObject,
    mut v_ring_1351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1352_ =
        l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_1349_, v_ring_1351_);
    return v___x_1352_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_coreOfNat_elim___redArg(
    mut v_t_1353_: *mut leanh::LeanObject,
    mut v_coreOfNat_1354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1355_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(
        v_t_1353_,
        v_coreOfNat_1354_,
    );
    return v___x_1355_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_coreOfNat_elim(
    mut v_motive__6_1356_: *mut leanh::LeanObject,
    mut v_t_1357_: *mut leanh::LeanObject,
    mut v_h_1358_: *mut leanh::LeanObject,
    mut v_coreOfNat_1359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1360_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(
        v_t_1357_,
        v_coreOfNat_1359_,
    );
    return v___x_1360_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_neg_elim___redArg(
    mut v_t_1361_: *mut leanh::LeanObject,
    mut v_neg_1362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1363_ =
        l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_1361_, v_neg_1362_);
    return v___x_1363_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_neg_elim(
    mut v_motive__6_1364_: *mut leanh::LeanObject,
    mut v_t_1365_: *mut leanh::LeanObject,
    mut v_h_1366_: *mut leanh::LeanObject,
    mut v_neg_1367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1368_ =
        l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_1365_, v_neg_1367_);
    return v___x_1368_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst_elim___redArg(
    mut v_t_1369_: *mut leanh::LeanObject,
    mut v_subst_1370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1371_ =
        l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_1369_, v_subst_1370_);
    return v___x_1371_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst_elim(
    mut v_motive__6_1372_: *mut leanh::LeanObject,
    mut v_t_1373_: *mut leanh::LeanObject,
    mut v_h_1374_: *mut leanh::LeanObject,
    mut v_subst_1375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1376_ =
        l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_1373_, v_subst_1375_);
    return v___x_1376_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst1_elim___redArg(
    mut v_t_1377_: *mut leanh::LeanObject,
    mut v_subst1_1378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1379_ =
        l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_1377_, v_subst1_1378_);
    return v___x_1379_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst1_elim(
    mut v_motive__6_1380_: *mut leanh::LeanObject,
    mut v_t_1381_: *mut leanh::LeanObject,
    mut v_h_1382_: *mut leanh::LeanObject,
    mut v_subst1_1383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1384_ =
        l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_1381_, v_subst1_1383_);
    return v___x_1384_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_oneNeZero_elim___redArg(
    mut v_t_1385_: *mut leanh::LeanObject,
    mut v_oneNeZero_1386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1387_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(
        v_t_1385_,
        v_oneNeZero_1386_,
    );
    return v___x_1387_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_oneNeZero_elim(
    mut v_motive__6_1388_: *mut leanh::LeanObject,
    mut v_t_1389_: *mut leanh::LeanObject,
    mut v_h_1390_: *mut leanh::LeanObject,
    mut v_oneNeZero_1391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1392_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(
        v_t_1389_,
        v_oneNeZero_1391_,
    );
    return v___x_1392_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorIdx(
    mut v_x_1393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1393_) == 0 {
        let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1394_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1394_;
    } else {
        let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1395_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1395_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorIdx___boxed(
    mut v_x_1396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1397_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorIdx(v_x_1396_);
    leanh::lean_dec_ref(v_x_1396_);
    return v_res_1397_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(
    mut v_t_1398_: *mut leanh::LeanObject,
    mut v_k_1399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_1400_ = leanh::lean_ctor_get(v_t_1398_, 0);
    leanh::lean_inc_ref(v_c_1400_);
    leanh::lean_dec_ref(v_t_1398_);
    v___x_1401_ = leanh::lean_apply_1(v_k_1399_, v_c_1400_);
    return v___x_1401_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim(
    mut v_motive__7_1402_: *mut leanh::LeanObject,
    mut v_ctorIdx_1403_: *mut leanh::LeanObject,
    mut v_t_1404_: *mut leanh::LeanObject,
    mut v_h_1405_: *mut leanh::LeanObject,
    mut v_k_1406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1407_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_1404_, v_k_1406_);
    return v___x_1407_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___boxed(
    mut v_motive__7_1408_: *mut leanh::LeanObject,
    mut v_ctorIdx_1409_: *mut leanh::LeanObject,
    mut v_t_1410_: *mut leanh::LeanObject,
    mut v_h_1411_: *mut leanh::LeanObject,
    mut v_k_1412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1413_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim(
        v_motive__7_1408_,
        v_ctorIdx_1409_,
        v_t_1410_,
        v_h_1411_,
        v_k_1412_,
    );
    leanh::lean_dec(v_ctorIdx_1409_);
    return v_res_1413_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_UnsatProof_diseq_elim___redArg(
    mut v_t_1414_: *mut leanh::LeanObject,
    mut v_diseq_1415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1416_ =
        l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_1414_, v_diseq_1415_);
    return v___x_1416_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_UnsatProof_diseq_elim(
    mut v_motive__7_1417_: *mut leanh::LeanObject,
    mut v_t_1418_: *mut leanh::LeanObject,
    mut v_h_1419_: *mut leanh::LeanObject,
    mut v_diseq_1420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1421_ =
        l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_1418_, v_diseq_1420_);
    return v___x_1421_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_UnsatProof_lt_elim___redArg(
    mut v_t_1422_: *mut leanh::LeanObject,
    mut v_lt_1423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1424_ =
        l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_1422_, v_lt_1423_);
    return v___x_1424_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_UnsatProof_lt_elim(
    mut v_motive__7_1425_: *mut leanh::LeanObject,
    mut v_t_1426_: *mut leanh::LeanObject,
    mut v_h_1427_: *mut leanh::LeanObject,
    mut v_lt_1428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1429_ =
        l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_1426_, v_lt_1428_);
    return v___x_1429_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = leanh::lean_box(0);
    v___x_1434_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__1;
    v___x_1435_ = l_Lean_Expr_const___override(v___x_1434_, v___x_1433_);
    return v___x_1435_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1436_ = leanh::lean_box(0);
    v___x_1437_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2,
    );
    v___x_1438_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1438_, 0, v___x_1437_);
    leanh::lean_ctor_set(v___x_1438_, 1, v___x_1437_);
    leanh::lean_ctor_set(v___x_1438_, 2, v___x_1436_);
    leanh::lean_ctor_set(v___x_1438_, 3, v___x_1436_);
    return v___x_1438_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1439_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3,
    );
    v___x_1440_ = leanh::lean_box(0);
    v___x_1441_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1441_, 0, v___x_1440_);
    leanh::lean_ctor_set(v___x_1441_, 1, v___x_1439_);
    return v___x_1441_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr()
-> *mut leanh::LeanObject {
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4,
    );
    return v___x_1442_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1443_ = leanh::lean_box(0);
    v___x_1444_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2,
    );
    v___x_1445_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1445_, 0, v___x_1444_);
    leanh::lean_ctor_set(v___x_1445_, 1, v___x_1444_);
    leanh::lean_ctor_set(v___x_1445_, 2, v___x_1443_);
    leanh::lean_ctor_set(v___x_1445_, 3, v___x_1443_);
    return v___x_1445_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1446_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0,
    );
    v___x_1447_ = leanh::lean_box(0);
    v___x_1448_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1448_, 0, v___x_1447_);
    leanh::lean_ctor_set(v___x_1448_, 1, v___x_1446_);
    return v___x_1448_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr()
-> *mut leanh::LeanObject {
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1449_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1,
    );
    return v___x_1449_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1450_ = leanh::lean_unsigned_to_nat(32);
    v___x_1451_ = lean_mk_empty_array_with_capacity(v___x_1450_);
    v___x_1452_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1452_, 0, v___x_1451_);
    return v___x_1452_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1453_: usize = 0;
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1453_ = 5usize;
    v___x_1454_ = leanh::lean_unsigned_to_nat(0);
    v___x_1455_ = leanh::lean_unsigned_to_nat(32);
    v___x_1456_ = lean_mk_empty_array_with_capacity(v___x_1455_);
    v___x_1457_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0,
    );
    v___x_1458_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1458_, 0, v___x_1457_);
    leanh::lean_ctor_set(v___x_1458_, 1, v___x_1456_);
    leanh::lean_ctor_set(v___x_1458_, 2, v___x_1454_);
    leanh::lean_ctor_set(v___x_1458_, 3, v___x_1454_);
    leanh::lean_ctor_set_usize(v___x_1458_, 4, v___x_1453_);
    return v___x_1458_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1459_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1459_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1460_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2,
    );
    v___x_1461_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1461_, 0, v___x_1460_);
    return v___x_1461_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: u8 = 0;
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1462_ = leanh::lean_box(0);
    v___x_1463_ = 0;
    v___x_1464_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3,
    );
    v___x_1465_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1,
    );
    v___x_1466_ = leanh::lean_box(0);
    v___x_1467_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2,
    );
    v___x_1468_ = leanh::lean_box(0);
    v___x_1469_ = leanh::lean_unsigned_to_nat(0);
    v___x_1470_ = leanh::lean_alloc_ctor(0, 42, (1) as u32);
    leanh::lean_ctor_set(v___x_1470_, 0, v___x_1469_);
    leanh::lean_ctor_set(v___x_1470_, 1, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 2, v___x_1467_);
    leanh::lean_ctor_set(v___x_1470_, 3, v___x_1466_);
    leanh::lean_ctor_set(v___x_1470_, 4, v___x_1467_);
    leanh::lean_ctor_set(v___x_1470_, 5, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 6, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 7, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 8, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 9, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 10, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 11, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 12, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 13, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 14, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 15, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 16, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 17, v___x_1467_);
    leanh::lean_ctor_set(v___x_1470_, 18, v___x_1467_);
    leanh::lean_ctor_set(v___x_1470_, 19, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 20, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 21, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 22, v___x_1467_);
    leanh::lean_ctor_set(v___x_1470_, 23, v___x_1467_);
    leanh::lean_ctor_set(v___x_1470_, 24, v___x_1467_);
    leanh::lean_ctor_set(v___x_1470_, 25, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 26, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 27, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 28, v___x_1467_);
    leanh::lean_ctor_set(v___x_1470_, 29, v___x_1467_);
    leanh::lean_ctor_set(v___x_1470_, 30, v___x_1465_);
    leanh::lean_ctor_set(v___x_1470_, 31, v___x_1464_);
    leanh::lean_ctor_set(v___x_1470_, 32, v___x_1465_);
    leanh::lean_ctor_set(v___x_1470_, 33, v___x_1465_);
    leanh::lean_ctor_set(v___x_1470_, 34, v___x_1465_);
    leanh::lean_ctor_set(v___x_1470_, 35, v___x_1465_);
    leanh::lean_ctor_set(v___x_1470_, 36, v___x_1468_);
    leanh::lean_ctor_set(v___x_1470_, 37, v___x_1464_);
    leanh::lean_ctor_set(v___x_1470_, 38, v___x_1465_);
    leanh::lean_ctor_set(v___x_1470_, 39, v___x_1462_);
    leanh::lean_ctor_set(v___x_1470_, 40, v___x_1465_);
    leanh::lean_ctor_set(v___x_1470_, 41, v___x_1465_);
    leanh::lean_ctor_set_uint8(
        v___x_1470_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 42) as u32,
        v___x_1463_,
    );
    return v___x_1470_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default()
-> *mut leanh::LeanObject {
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1471_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4,
    );
    return v___x_1471_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct()
-> *mut leanh::LeanObject {
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1472_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
    return v___x_1472_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1473_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1473_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1474_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0);
    v___x_1475_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1475_, 0, v___x_1474_);
    return v___x_1475_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0(
    mut v_00_u03b2_1476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1477_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__1);
    return v___x_1477_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1480_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1480_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1481_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1,
    );
    v___x_1482_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1482_, 0, v___x_1481_);
    return v___x_1482_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1483_ = leanh::lean_unsigned_to_nat(32);
    v___x_1484_ = lean_mk_empty_array_with_capacity(v___x_1483_);
    v___x_1485_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1485_, 0, v___x_1484_);
    return v___x_1485_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1486_: usize = 0;
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1486_ = 5usize;
    v___x_1487_ = leanh::lean_unsigned_to_nat(0);
    v___x_1488_ = leanh::lean_unsigned_to_nat(32);
    v___x_1489_ = lean_mk_empty_array_with_capacity(v___x_1488_);
    v___x_1490_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3,
    );
    v___x_1491_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1491_, 0, v___x_1490_);
    leanh::lean_ctor_set(v___x_1491_, 1, v___x_1489_);
    leanh::lean_ctor_set(v___x_1491_, 2, v___x_1487_);
    leanh::lean_ctor_set(v___x_1491_, 3, v___x_1487_);
    leanh::lean_ctor_set_usize(v___x_1491_, 4, v___x_1486_);
    return v___x_1491_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1492_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0(leanh::lean_box(0));
    return v___x_1492_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1493_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__5_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__5,
    );
    v___x_1494_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4,
    );
    v___x_1495_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2,
    );
    v___x_1496_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__0;
    v___x_1497_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
    leanh::lean_ctor_set(v___x_1497_, 0, v___x_1496_);
    leanh::lean_ctor_set(v___x_1497_, 1, v___x_1495_);
    leanh::lean_ctor_set(v___x_1497_, 2, v___x_1495_);
    leanh::lean_ctor_set(v___x_1497_, 3, v___x_1494_);
    leanh::lean_ctor_set(v___x_1497_, 4, v___x_1493_);
    leanh::lean_ctor_set(v___x_1497_, 5, v___x_1496_);
    leanh::lean_ctor_set(v___x_1497_, 6, v___x_1495_);
    leanh::lean_ctor_set(v___x_1497_, 7, v___x_1495_);
    return v___x_1497_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default()
-> *mut leanh::LeanObject {
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1498_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__6_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__6,
    );
    return v___x_1498_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState()
-> *mut leanh::LeanObject {
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1499_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default;
    return v___x_1499_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_(
    mut v___x_1500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1502_, 0, v___x_1500_);
    return v___x_1502_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2____boxed(
    mut v___x_1503_: *mut leanh::LeanObject,
    mut v___y_1504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1505_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_(v___x_1503_);
    return v_res_1505_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1506_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__6_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__6,
    );
    v___f_1507_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_1507_, 0, v___x_1506_);
    return v___f_1507_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1509_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_);
    v___x_1510_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_1509_);
    return v___x_1510_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2____boxed(
    mut v_a_1511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1512_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_();
    return v_res_1512_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ring_CommSolver(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ordered_Linarith(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr =
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr);
    l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr =
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr);
    l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default =
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default);
    l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct =
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct);
    l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default =
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default);
    l_Lean_Meta_Grind_Arith_Linear_instInhabitedState =
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedState);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Grind_Arith_Linear_linearExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_linearExt);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ring_CommSolver(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Ordered_Linarith(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
}