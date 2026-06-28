// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
// Imports: Init.Data.Int.Linear Lean.Meta.Tactic.Grind.Arith.CommRing.Types Lean.Meta.Tactic.Grind.Arith.Cutsat.ToIntInfo
use crate::r#gen::Init::Data::Int::Linear::{
    initialize_Init_Data_Int_Linear, runtime_initialize_Init_Data_Int_Linear,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::l_Lean_Expr_const___override;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::ToIntInfo::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l_Lean_Meta_Grind_registerSolverExtension___redArg;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint64_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_mul, lean_nat_sub,
    lean_uint64_mix_hash,
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__1_value:
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__1_value)
            as *mut crate::leanh::LeanObject,
        17542774118954891045 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v_natZero_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_natZero_966_ = crate::leanh::lean_unsigned_to_nat(0);
    v_intZero_967_ = lean_nat_to_int(v_natZero_966_);
    return v_intZero_967_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(
    mut v_x_968_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_k_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: u64 = 0;
    let mut v_intZero_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_972_: u8 = 0;
    let mut v_a_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: u64 = 0;
    let mut v___x_977_: u64 = 0;
    let mut v_abs_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: u64 = 0;
    let mut v___x_985_: u64 = 0;
    let mut v_k_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: u64 = 0;
    let mut v___y_991_: u64 = 0;
    let mut v___x_992_: u64 = 0;
    let mut v___x_993_: u64 = 0;
    let mut v___x_994_: u64 = 0;
    let mut v___x_995_: u64 = 0;
    let mut v___x_996_: u64 = 0;
    let mut v_intZero_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_998_: u8 = 0;
    let mut v_a_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: u64 = 0;
    let mut v_abs_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_968_) == 0 {
                    v_k_969_ = crate::leanh::lean_ctor_get(v_x_968_, 0);
                    v___x_970_ = 0u64;
                    v_intZero_971_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
                    v_isNeg_972_ = lean_int_dec_lt(v_k_969_, v_intZero_971_);
                    if v_isNeg_972_ == 0 {
                        v_a_973_ = lean_nat_abs(v_k_969_);
                        v___x_974_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_975_ = lean_nat_mul(v___x_974_, v_a_973_);
                        crate::leanh::lean_dec(v_a_973_);
                        v___x_976_ = lean_uint64_of_nat(v___x_975_);
                        crate::leanh::lean_dec(v___x_975_);
                        v___x_977_ = lean_uint64_mix_hash(v___x_970_, v___x_976_);
                        return v___x_977_;
                    } else {
                        v_abs_978_ = lean_nat_abs(v_k_969_);
                        v_one_979_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_a_980_ = lean_nat_sub(v_abs_978_, v_one_979_);
                        crate::leanh::lean_dec(v_abs_978_);
                        v___x_981_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_982_ = lean_nat_mul(v___x_981_, v_a_980_);
                        crate::leanh::lean_dec(v_a_980_);
                        v___x_983_ = lean_nat_add(v___x_982_, v_one_979_);
                        crate::leanh::lean_dec(v___x_982_);
                        v___x_984_ = lean_uint64_of_nat(v___x_983_);
                        crate::leanh::lean_dec(v___x_983_);
                        v___x_985_ = lean_uint64_mix_hash(v___x_970_, v___x_984_);
                        return v___x_985_;
                    }
                } else {
                    v_k_986_ = crate::leanh::lean_ctor_get(v_x_968_, 0);
                    v_v_987_ = crate::leanh::lean_ctor_get(v_x_968_, 1);
                    v_p_988_ = crate::leanh::lean_ctor_get(v_x_968_, 2);
                    v___x_989_ = 1u64;
                    v_intZero_997_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
                    v_isNeg_998_ = lean_int_dec_lt(v_k_986_, v_intZero_997_);
                    if v_isNeg_998_ == 0 {
                        v_a_999_ = lean_nat_abs(v_k_986_);
                        v___x_1000_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_1001_ = lean_nat_mul(v___x_1000_, v_a_999_);
                        crate::leanh::lean_dec(v_a_999_);
                        v___x_1002_ = lean_uint64_of_nat(v___x_1001_);
                        crate::leanh::lean_dec(v___x_1001_);
                        v___y_991_ = v___x_1002_;
                        state = 1;
                        continue;
                    } else {
                        v_abs_1003_ = lean_nat_abs(v_k_986_);
                        v_one_1004_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_a_1005_ = lean_nat_sub(v_abs_1003_, v_one_1004_);
                        crate::leanh::lean_dec(v_abs_1003_);
                        v___x_1006_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_1007_ = lean_nat_mul(v___x_1006_, v_a_1005_);
                        crate::leanh::lean_dec(v_a_1005_);
                        v___x_1008_ = lean_nat_add(v___x_1007_, v_one_1004_);
                        crate::leanh::lean_dec(v___x_1007_);
                        v___x_1009_ = lean_uint64_of_nat(v___x_1008_);
                        crate::leanh::lean_dec(v___x_1008_);
                        v___y_991_ = v___x_1009_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_992_ = lean_uint64_mix_hash(v___x_989_, v___y_991_);
                v___x_993_ = lean_uint64_of_nat(v_v_987_);
                v___x_994_ = lean_uint64_mix_hash(v___x_992_, v___x_993_);
                v___x_995_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_p_988_);
                v___x_996_ = lean_uint64_mix_hash(v___x_994_, v___x_995_);
                return v___x_996_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___boxed(
    mut v_x_1010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1011_: u64 = 0;
    let mut v_r_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1011_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_x_1010_);
    crate::leanh::lean_dec_ref(v_x_1010_);
    v_r_1012_ = crate::leanh::lean_box_uint64(v_res_1011_);
    return v_r_1012_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx(
    mut v_x_1015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1015_) {
        0 => {
            let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1016_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1016_;
        }
        1 => {
            let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1017_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1017_;
        }
        2 => {
            let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1018_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1018_;
        }
        3 => {
            let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1019_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_1019_;
        }
        4 => {
            let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1020_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_1020_;
        }
        5 => {
            let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1021_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_1021_;
        }
        6 => {
            let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1022_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_1022_;
        }
        7 => {
            let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1023_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_1023_;
        }
        8 => {
            let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1024_ = crate::leanh::lean_unsigned_to_nat(8);
            return v___x_1024_;
        }
        9 => {
            let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1025_ = crate::leanh::lean_unsigned_to_nat(9);
            return v___x_1025_;
        }
        10 => {
            let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1026_ = crate::leanh::lean_unsigned_to_nat(10);
            return v___x_1026_;
        }
        11 => {
            let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1027_ = crate::leanh::lean_unsigned_to_nat(11);
            return v___x_1027_;
        }
        12 => {
            let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1028_ = crate::leanh::lean_unsigned_to_nat(12);
            return v___x_1028_;
        }
        13 => {
            let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1029_ = crate::leanh::lean_unsigned_to_nat(13);
            return v___x_1029_;
        }
        14 => {
            let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1030_ = crate::leanh::lean_unsigned_to_nat(14);
            return v___x_1030_;
        }
        15 => {
            let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1031_ = crate::leanh::lean_unsigned_to_nat(15);
            return v___x_1031_;
        }
        _ => {
            let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1032_ = crate::leanh::lean_unsigned_to_nat(16);
            return v___x_1032_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___boxed(
    mut v_x_1033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1034_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx(v_x_1033_);
    crate::leanh::lean_dec_ref(v_x_1033_);
    return v_res_1034_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(
    mut v_t_1035_: *mut crate::leanh::LeanObject,
    mut v_k_1036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_1035_) {
        1 => {
            let mut v_a_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_u2081_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_u2082_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1037_ = crate::leanh::lean_ctor_get(v_t_1035_, 0);
            crate::leanh::lean_inc_ref(v_a_1037_);
            v_b_1038_ = crate::leanh::lean_ctor_get(v_t_1035_, 1);
            crate::leanh::lean_inc_ref(v_b_1038_);
            v_p_u2081_1039_ = crate::leanh::lean_ctor_get(v_t_1035_, 2);
            crate::leanh::lean_inc_ref(v_p_u2081_1039_);
            v_p_u2082_1040_ = crate::leanh::lean_ctor_get(v_t_1035_, 3);
            crate::leanh::lean_inc_ref(v_p_u2082_1040_);
            crate::leanh::lean_dec_ref_known(v_t_1035_, 4);
            v___x_1041_ = crate::leanh::lean_apply_4(
                v_k_1036_,
                v_a_1037_,
                v_b_1038_,
                v_p_u2081_1039_,
                v_p_u2082_1040_,
            );
            return v___x_1041_;
        }
        2 => {
            let mut v_a_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toIntThm_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1042_ = crate::leanh::lean_ctor_get(v_t_1035_, 0);
            crate::leanh::lean_inc_ref(v_a_1042_);
            v_b_1043_ = crate::leanh::lean_ctor_get(v_t_1035_, 1);
            crate::leanh::lean_inc_ref(v_b_1043_);
            v_toIntThm_1044_ = crate::leanh::lean_ctor_get(v_t_1035_, 2);
            crate::leanh::lean_inc_ref(v_toIntThm_1044_);
            v_lhs_1045_ = crate::leanh::lean_ctor_get(v_t_1035_, 3);
            crate::leanh::lean_inc_ref(v_lhs_1045_);
            v_rhs_1046_ = crate::leanh::lean_ctor_get(v_t_1035_, 4);
            crate::leanh::lean_inc_ref(v_rhs_1046_);
            crate::leanh::lean_dec_ref_known(v_t_1035_, 5);
            v___x_1047_ = crate::leanh::lean_apply_5(
                v_k_1036_,
                v_a_1042_,
                v_b_1043_,
                v_toIntThm_1044_,
                v_lhs_1045_,
                v_rhs_1046_,
            );
            return v___x_1047_;
        }
        4 => {
            let mut v_h_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_e_x27_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_h_1048_ = crate::leanh::lean_ctor_get(v_t_1035_, 0);
            crate::leanh::lean_inc_ref(v_h_1048_);
            v_x_1049_ = crate::leanh::lean_ctor_get(v_t_1035_, 1);
            crate::leanh::lean_inc(v_x_1049_);
            v_e_x27_1050_ = crate::leanh::lean_ctor_get(v_t_1035_, 2);
            crate::leanh::lean_inc_ref(v_e_x27_1050_);
            crate::leanh::lean_dec_ref_known(v_t_1035_, 3);
            v___x_1051_ =
                crate::leanh::lean_apply_3(v_k_1036_, v_h_1048_, v_x_1049_, v_e_x27_1050_);
            return v___x_1051_;
        }
        5 => {
            let mut v_c_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_1052_ = crate::leanh::lean_ctor_get(v_t_1035_, 0);
            crate::leanh::lean_inc_ref(v_c_1052_);
            crate::leanh::lean_dec_ref_known(v_t_1035_, 1);
            v___x_1053_ = crate::leanh::lean_apply_1(v_k_1036_, v_c_1052_);
            return v___x_1053_;
        }
        6 => {
            let mut v_c_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_1054_ = crate::leanh::lean_ctor_get(v_t_1035_, 0);
            crate::leanh::lean_inc_ref(v_c_1054_);
            crate::leanh::lean_dec_ref_known(v_t_1035_, 1);
            v___x_1055_ = crate::leanh::lean_apply_1(v_k_1036_, v_c_1054_);
            return v___x_1055_;
        }
        7 => {
            let mut v_x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_1056_ = crate::leanh::lean_ctor_get(v_t_1035_, 0);
            crate::leanh::lean_inc(v_x_1056_);
            v_c_u2081_1057_ = crate::leanh::lean_ctor_get(v_t_1035_, 1);
            crate::leanh::lean_inc_ref(v_c_u2081_1057_);
            v_c_u2082_1058_ = crate::leanh::lean_ctor_get(v_t_1035_, 2);
            crate::leanh::lean_inc_ref(v_c_u2082_1058_);
            crate::leanh::lean_dec_ref_known(v_t_1035_, 3);
            v___x_1059_ =
                crate::leanh::lean_apply_3(v_k_1036_, v_x_1056_, v_c_u2081_1057_, v_c_u2082_1058_);
            return v___x_1059_;
        }
        9 => {
            let mut v_c_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_1060_ = crate::leanh::lean_ctor_get(v_t_1035_, 0);
            crate::leanh::lean_inc_ref(v_c_1060_);
            crate::leanh::lean_dec_ref_known(v_t_1035_, 1);
            v___x_1061_ = crate::leanh::lean_apply_1(v_k_1036_, v_c_1060_);
            return v___x_1061_;
        }
        10 => {
            let mut v_c_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_e_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_1062_ = crate::leanh::lean_ctor_get(v_t_1035_, 0);
            crate::leanh::lean_inc_ref(v_c_1062_);
            v_e_1063_ = crate::leanh::lean_ctor_get(v_t_1035_, 1);
            crate::leanh::lean_inc_ref(v_e_1063_);
            v_p_1064_ = crate::leanh::lean_ctor_get(v_t_1035_, 2);
            crate::leanh::lean_inc_ref(v_p_1064_);
            crate::leanh::lean_dec_ref_known(v_t_1035_, 3);
            v___x_1065_ = crate::leanh::lean_apply_3(v_k_1036_, v_c_1062_, v_e_1063_, v_p_1064_);
            return v___x_1065_;
        }
        11 => {
            let mut v_e_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_re_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rp_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_x27_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_e_1066_ = crate::leanh::lean_ctor_get(v_t_1035_, 0);
            crate::leanh::lean_inc_ref(v_e_1066_);
            v_p_1067_ = crate::leanh::lean_ctor_get(v_t_1035_, 1);
            crate::leanh::lean_inc_ref(v_p_1067_);
            v_re_1068_ = crate::leanh::lean_ctor_get(v_t_1035_, 2);
            crate::leanh::lean_inc_ref(v_re_1068_);
            v_rp_1069_ = crate::leanh::lean_ctor_get(v_t_1035_, 3);
            crate::leanh::lean_inc_ref(v_rp_1069_);
            v_p_x27_1070_ = crate::leanh::lean_ctor_get(v_t_1035_, 4);
            crate::leanh::lean_inc_ref(v_p_x27_1070_);
            crate::leanh::lean_dec_ref_known(v_t_1035_, 5);
            v___x_1071_ = crate::leanh::lean_apply_5(
                v_k_1036_,
                v_e_1066_,
                v_p_1067_,
                v_re_1068_,
                v_rp_1069_,
                v_p_x27_1070_,
            );
            return v___x_1071_;
        }
        12 => {
            let mut v_h_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_e_x27_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_re_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rp_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_x27_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_h_1072_ = crate::leanh::lean_ctor_get(v_t_1035_, 0);
            crate::leanh::lean_inc_ref(v_h_1072_);
            v_x_1073_ = crate::leanh::lean_ctor_get(v_t_1035_, 1);
            crate::leanh::lean_inc(v_x_1073_);
            v_e_x27_1074_ = crate::leanh::lean_ctor_get(v_t_1035_, 2);
            crate::leanh::lean_inc_ref(v_e_x27_1074_);
            v_p_1075_ = crate::leanh::lean_ctor_get(v_t_1035_, 3);
            crate::leanh::lean_inc_ref(v_p_1075_);
            v_re_1076_ = crate::leanh::lean_ctor_get(v_t_1035_, 4);
            crate::leanh::lean_inc_ref(v_re_1076_);
            v_rp_1077_ = crate::leanh::lean_ctor_get(v_t_1035_, 5);
            crate::leanh::lean_inc_ref(v_rp_1077_);
            v_p_x27_1078_ = crate::leanh::lean_ctor_get(v_t_1035_, 6);
            crate::leanh::lean_inc_ref(v_p_x27_1078_);
            crate::leanh::lean_dec_ref_known(v_t_1035_, 7);
            v___x_1079_ = crate::leanh::lean_apply_7(
                v_k_1036_,
                v_h_1072_,
                v_x_1073_,
                v_e_x27_1074_,
                v_p_1075_,
                v_re_1076_,
                v_rp_1077_,
                v_p_x27_1078_,
            );
            return v___x_1079_;
        }
        13 => {
            let mut v_a_x3f_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_cs_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_x3f_1080_ = crate::leanh::lean_ctor_get(v_t_1035_, 0);
            crate::leanh::lean_inc(v_a_x3f_1080_);
            v_cs_1081_ = crate::leanh::lean_ctor_get(v_t_1035_, 1);
            crate::leanh::lean_inc_ref(v_cs_1081_);
            crate::leanh::lean_dec_ref_known(v_t_1035_, 2);
            v___x_1082_ = crate::leanh::lean_apply_2(v_k_1036_, v_a_x3f_1080_, v_cs_1081_);
            return v___x_1082_;
        }
        14 => {
            let mut v_k_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_x3f_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_k_1083_ = crate::leanh::lean_ctor_get(v_t_1035_, 0);
            crate::leanh::lean_inc(v_k_1083_);
            v_y_x3f_1084_ = crate::leanh::lean_ctor_get(v_t_1035_, 1);
            crate::leanh::lean_inc(v_y_x3f_1084_);
            v_c_1085_ = crate::leanh::lean_ctor_get(v_t_1035_, 2);
            crate::leanh::lean_inc_ref(v_c_1085_);
            crate::leanh::lean_dec_ref_known(v_t_1035_, 3);
            v___x_1086_ =
                crate::leanh::lean_apply_3(v_k_1036_, v_k_1083_, v_y_x3f_1084_, v_c_1085_);
            return v___x_1086_;
        }
        15 => {
            let mut v_k_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_x3f_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_k_1087_ = crate::leanh::lean_ctor_get(v_t_1035_, 0);
            crate::leanh::lean_inc(v_k_1087_);
            v_y_x3f_1088_ = crate::leanh::lean_ctor_get(v_t_1035_, 1);
            crate::leanh::lean_inc(v_y_x3f_1088_);
            v_c_1089_ = crate::leanh::lean_ctor_get(v_t_1035_, 2);
            crate::leanh::lean_inc_ref(v_c_1089_);
            crate::leanh::lean_dec_ref_known(v_t_1035_, 3);
            v___x_1090_ =
                crate::leanh::lean_apply_3(v_k_1036_, v_k_1087_, v_y_x3f_1088_, v_c_1089_);
            return v___x_1090_;
        }
        16 => {
            let mut v_ka_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ca_x3f_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_kb_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_cb_x3f_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_ka_1091_ = crate::leanh::lean_ctor_get(v_t_1035_, 0);
            crate::leanh::lean_inc(v_ka_1091_);
            v_ca_x3f_1092_ = crate::leanh::lean_ctor_get(v_t_1035_, 1);
            crate::leanh::lean_inc(v_ca_x3f_1092_);
            v_kb_1093_ = crate::leanh::lean_ctor_get(v_t_1035_, 2);
            crate::leanh::lean_inc(v_kb_1093_);
            v_cb_x3f_1094_ = crate::leanh::lean_ctor_get(v_t_1035_, 3);
            crate::leanh::lean_inc(v_cb_x3f_1094_);
            crate::leanh::lean_dec_ref_known(v_t_1035_, 4);
            v___x_1095_ = crate::leanh::lean_apply_4(
                v_k_1036_,
                v_ka_1091_,
                v_ca_x3f_1092_,
                v_kb_1093_,
                v_cb_x3f_1094_,
            );
            return v___x_1095_;
        }
        _ => {
            let mut v_a_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_zero_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1096_ = crate::leanh::lean_ctor_get(v_t_1035_, 0);
            crate::leanh::lean_inc_ref(v_a_1096_);
            v_zero_1097_ = crate::leanh::lean_ctor_get(v_t_1035_, 1);
            crate::leanh::lean_inc_ref(v_zero_1097_);
            crate::leanh::lean_dec_ref(v_t_1035_);
            v___x_1098_ = crate::leanh::lean_apply_2(v_k_1036_, v_a_1096_, v_zero_1097_);
            return v___x_1098_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(
    mut v_motive__2_1099_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1100_: *mut crate::leanh::LeanObject,
    mut v_t_1101_: *mut crate::leanh::LeanObject,
    mut v_h_1102_: *mut crate::leanh::LeanObject,
    mut v_k_1103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1104_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1101_, v_k_1103_);
    return v___x_1104_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___boxed(
    mut v_motive__2_1105_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1106_: *mut crate::leanh::LeanObject,
    mut v_t_1107_: *mut crate::leanh::LeanObject,
    mut v_h_1108_: *mut crate::leanh::LeanObject,
    mut v_k_1109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1110_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(
        v_motive__2_1105_,
        v_ctorIdx_1106_,
        v_t_1107_,
        v_h_1108_,
        v_k_1109_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1106_);
    return v_res_1110_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim___redArg(
    mut v_t_1111_: *mut crate::leanh::LeanObject,
    mut v_core0_1112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1113_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1111_, v_core0_1112_);
    return v___x_1113_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim(
    mut v_motive__2_1114_: *mut crate::leanh::LeanObject,
    mut v_t_1115_: *mut crate::leanh::LeanObject,
    mut v_h_1116_: *mut crate::leanh::LeanObject,
    mut v_core0_1117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1118_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1115_, v_core0_1117_);
    return v___x_1118_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim___redArg(
    mut v_t_1119_: *mut crate::leanh::LeanObject,
    mut v_core_1120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1121_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1119_, v_core_1120_);
    return v___x_1121_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim(
    mut v_motive__2_1122_: *mut crate::leanh::LeanObject,
    mut v_t_1123_: *mut crate::leanh::LeanObject,
    mut v_h_1124_: *mut crate::leanh::LeanObject,
    mut v_core_1125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1126_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1123_, v_core_1125_);
    return v___x_1126_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim___redArg(
    mut v_t_1127_: *mut crate::leanh::LeanObject,
    mut v_coreToInt_1128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1129_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1127_, v_coreToInt_1128_);
    return v___x_1129_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim(
    mut v_motive__2_1130_: *mut crate::leanh::LeanObject,
    mut v_t_1131_: *mut crate::leanh::LeanObject,
    mut v_h_1132_: *mut crate::leanh::LeanObject,
    mut v_coreToInt_1133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1134_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1131_, v_coreToInt_1133_);
    return v___x_1134_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim___redArg(
    mut v_t_1135_: *mut crate::leanh::LeanObject,
    mut v_defn_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1137_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1135_, v_defn_1136_);
    return v___x_1137_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim(
    mut v_motive__2_1138_: *mut crate::leanh::LeanObject,
    mut v_t_1139_: *mut crate::leanh::LeanObject,
    mut v_h_1140_: *mut crate::leanh::LeanObject,
    mut v_defn_1141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1142_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1139_, v_defn_1141_);
    return v___x_1142_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNat_elim___redArg(
    mut v_t_1143_: *mut crate::leanh::LeanObject,
    mut v_defnNat_1144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1145_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1143_, v_defnNat_1144_);
    return v___x_1145_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNat_elim(
    mut v_motive__2_1146_: *mut crate::leanh::LeanObject,
    mut v_t_1147_: *mut crate::leanh::LeanObject,
    mut v_h_1148_: *mut crate::leanh::LeanObject,
    mut v_defnNat_1149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1150_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1147_, v_defnNat_1149_);
    return v___x_1150_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim___redArg(
    mut v_t_1151_: *mut crate::leanh::LeanObject,
    mut v_norm_1152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1153_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1151_, v_norm_1152_);
    return v___x_1153_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim(
    mut v_motive__2_1154_: *mut crate::leanh::LeanObject,
    mut v_t_1155_: *mut crate::leanh::LeanObject,
    mut v_h_1156_: *mut crate::leanh::LeanObject,
    mut v_norm_1157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1158_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1155_, v_norm_1157_);
    return v___x_1158_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim___redArg(
    mut v_t_1159_: *mut crate::leanh::LeanObject,
    mut v_divCoeffs_1160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1161_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1159_, v_divCoeffs_1160_);
    return v___x_1161_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim(
    mut v_motive__2_1162_: *mut crate::leanh::LeanObject,
    mut v_t_1163_: *mut crate::leanh::LeanObject,
    mut v_h_1164_: *mut crate::leanh::LeanObject,
    mut v_divCoeffs_1165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1166_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1163_, v_divCoeffs_1165_);
    return v___x_1166_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim___redArg(
    mut v_t_1167_: *mut crate::leanh::LeanObject,
    mut v_subst_1168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1169_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1167_, v_subst_1168_);
    return v___x_1169_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim(
    mut v_motive__2_1170_: *mut crate::leanh::LeanObject,
    mut v_t_1171_: *mut crate::leanh::LeanObject,
    mut v_h_1172_: *mut crate::leanh::LeanObject,
    mut v_subst_1173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1174_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1171_, v_subst_1173_);
    return v___x_1174_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim___redArg(
    mut v_t_1175_: *mut crate::leanh::LeanObject,
    mut v_ofLeGe_1176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1177_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1175_, v_ofLeGe_1176_);
    return v___x_1177_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim(
    mut v_motive__2_1178_: *mut crate::leanh::LeanObject,
    mut v_t_1179_: *mut crate::leanh::LeanObject,
    mut v_h_1180_: *mut crate::leanh::LeanObject,
    mut v_ofLeGe_1181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1179_, v_ofLeGe_1181_);
    return v___x_1182_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim___redArg(
    mut v_t_1183_: *mut crate::leanh::LeanObject,
    mut v_reorder_1184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1185_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1183_, v_reorder_1184_);
    return v___x_1185_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim(
    mut v_motive__2_1186_: *mut crate::leanh::LeanObject,
    mut v_t_1187_: *mut crate::leanh::LeanObject,
    mut v_h_1188_: *mut crate::leanh::LeanObject,
    mut v_reorder_1189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1190_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1187_, v_reorder_1189_);
    return v___x_1190_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim___redArg(
    mut v_t_1191_: *mut crate::leanh::LeanObject,
    mut v_commRingNorm_1192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1193_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(
        v_t_1191_,
        v_commRingNorm_1192_,
    );
    return v___x_1193_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim(
    mut v_motive__2_1194_: *mut crate::leanh::LeanObject,
    mut v_t_1195_: *mut crate::leanh::LeanObject,
    mut v_h_1196_: *mut crate::leanh::LeanObject,
    mut v_commRingNorm_1197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1198_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(
        v_t_1195_,
        v_commRingNorm_1197_,
    );
    return v___x_1198_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim___redArg(
    mut v_t_1199_: *mut crate::leanh::LeanObject,
    mut v_defnCommRing_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1201_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(
        v_t_1199_,
        v_defnCommRing_1200_,
    );
    return v___x_1201_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim(
    mut v_motive__2_1202_: *mut crate::leanh::LeanObject,
    mut v_t_1203_: *mut crate::leanh::LeanObject,
    mut v_h_1204_: *mut crate::leanh::LeanObject,
    mut v_defnCommRing_1205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1206_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(
        v_t_1203_,
        v_defnCommRing_1205_,
    );
    return v___x_1206_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNatCommRing_elim___redArg(
    mut v_t_1207_: *mut crate::leanh::LeanObject,
    mut v_defnNatCommRing_1208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1209_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(
        v_t_1207_,
        v_defnNatCommRing_1208_,
    );
    return v___x_1209_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNatCommRing_elim(
    mut v_motive__2_1210_: *mut crate::leanh::LeanObject,
    mut v_t_1211_: *mut crate::leanh::LeanObject,
    mut v_h_1212_: *mut crate::leanh::LeanObject,
    mut v_defnNatCommRing_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1214_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(
        v_t_1211_,
        v_defnNatCommRing_1213_,
    );
    return v___x_1214_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim___redArg(
    mut v_t_1215_: *mut crate::leanh::LeanObject,
    mut v_mul_1216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1217_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1215_, v_mul_1216_);
    return v___x_1217_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim(
    mut v_motive__2_1218_: *mut crate::leanh::LeanObject,
    mut v_t_1219_: *mut crate::leanh::LeanObject,
    mut v_h_1220_: *mut crate::leanh::LeanObject,
    mut v_mul_1221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1222_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1219_, v_mul_1221_);
    return v___x_1222_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim___redArg(
    mut v_t_1223_: *mut crate::leanh::LeanObject,
    mut v_div_1224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1225_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1223_, v_div_1224_);
    return v___x_1225_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim(
    mut v_motive__2_1226_: *mut crate::leanh::LeanObject,
    mut v_t_1227_: *mut crate::leanh::LeanObject,
    mut v_h_1228_: *mut crate::leanh::LeanObject,
    mut v_div_1229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1230_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1227_, v_div_1229_);
    return v___x_1230_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim___redArg(
    mut v_t_1231_: *mut crate::leanh::LeanObject,
    mut v_mod_1232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1233_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1231_, v_mod_1232_);
    return v___x_1233_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim(
    mut v_motive__2_1234_: *mut crate::leanh::LeanObject,
    mut v_t_1235_: *mut crate::leanh::LeanObject,
    mut v_h_1236_: *mut crate::leanh::LeanObject,
    mut v_mod_1237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1238_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1235_, v_mod_1237_);
    return v___x_1238_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim___redArg(
    mut v_t_1239_: *mut crate::leanh::LeanObject,
    mut v_pow_1240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1241_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1239_, v_pow_1240_);
    return v___x_1241_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim(
    mut v_motive__2_1242_: *mut crate::leanh::LeanObject,
    mut v_t_1243_: *mut crate::leanh::LeanObject,
    mut v_h_1244_: *mut crate::leanh::LeanObject,
    mut v_pow_1245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1246_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1243_, v_pow_1245_);
    return v___x_1246_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx(
    mut v_x_1247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1247_) == 0 {
        let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1248_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1248_;
    } else {
        let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1249_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1249_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___boxed(
    mut v_x_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1251_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx(v_x_1250_);
    crate::leanh::lean_dec_ref(v_x_1250_);
    return v_res_1251_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(
    mut v_t_1252_: *mut crate::leanh::LeanObject,
    mut v_k_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1252_) == 0 {
        let mut v_h_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_h_1254_ = crate::leanh::lean_ctor_get(v_t_1252_, 0);
        crate::leanh::lean_inc(v_h_1254_);
        crate::leanh::lean_dec_ref_known(v_t_1252_, 1);
        v___x_1255_ = crate::leanh::lean_apply_1(v_k_1253_, v_h_1254_);
        return v___x_1255_;
    } else {
        let mut v_hs_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_decVars_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_hs_1256_ = crate::leanh::lean_ctor_get(v_t_1252_, 0);
        crate::leanh::lean_inc_ref(v_hs_1256_);
        v_decVars_1257_ = crate::leanh::lean_ctor_get(v_t_1252_, 1);
        crate::leanh::lean_inc_ref(v_decVars_1257_);
        crate::leanh::lean_dec_ref_known(v_t_1252_, 2);
        v___x_1258_ = crate::leanh::lean_apply_2(v_k_1253_, v_hs_1256_, v_decVars_1257_);
        return v___x_1258_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(
    mut v_motive__6_1259_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1260_: *mut crate::leanh::LeanObject,
    mut v_t_1261_: *mut crate::leanh::LeanObject,
    mut v_h_1262_: *mut crate::leanh::LeanObject,
    mut v_k_1263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1264_ =
        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_1261_, v_k_1263_);
    return v___x_1264_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___boxed(
    mut v_motive__6_1265_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1266_: *mut crate::leanh::LeanObject,
    mut v_t_1267_: *mut crate::leanh::LeanObject,
    mut v_h_1268_: *mut crate::leanh::LeanObject,
    mut v_k_1269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1270_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(
        v_motive__6_1265_,
        v_ctorIdx_1266_,
        v_t_1267_,
        v_h_1268_,
        v_k_1269_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1266_);
    return v_res_1270_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim___redArg(
    mut v_t_1271_: *mut crate::leanh::LeanObject,
    mut v_dec_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1273_ =
        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_1271_, v_dec_1272_);
    return v___x_1273_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim(
    mut v_motive__6_1274_: *mut crate::leanh::LeanObject,
    mut v_t_1275_: *mut crate::leanh::LeanObject,
    mut v_h_1276_: *mut crate::leanh::LeanObject,
    mut v_dec_1277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1278_ =
        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_1275_, v_dec_1277_);
    return v___x_1278_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim___redArg(
    mut v_t_1279_: *mut crate::leanh::LeanObject,
    mut v_last_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ =
        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_1279_, v_last_1280_);
    return v___x_1281_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim(
    mut v_motive__6_1282_: *mut crate::leanh::LeanObject,
    mut v_t_1283_: *mut crate::leanh::LeanObject,
    mut v_h_1284_: *mut crate::leanh::LeanObject,
    mut v_last_1285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1286_ =
        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_1283_, v_last_1285_);
    return v___x_1286_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx(
    mut v_x_1287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1287_) {
        0 => {
            let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1288_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1288_;
        }
        1 => {
            let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1289_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1289_;
        }
        2 => {
            let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1290_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1290_;
        }
        3 => {
            let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1291_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_1291_;
        }
        4 => {
            let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1292_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_1292_;
        }
        5 => {
            let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1293_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_1293_;
        }
        6 => {
            let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1294_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_1294_;
        }
        7 => {
            let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1295_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_1295_;
        }
        8 => {
            let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1296_ = crate::leanh::lean_unsigned_to_nat(8);
            return v___x_1296_;
        }
        9 => {
            let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1297_ = crate::leanh::lean_unsigned_to_nat(9);
            return v___x_1297_;
        }
        10 => {
            let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1298_ = crate::leanh::lean_unsigned_to_nat(10);
            return v___x_1298_;
        }
        11 => {
            let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1299_ = crate::leanh::lean_unsigned_to_nat(11);
            return v___x_1299_;
        }
        _ => {
            let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1300_ = crate::leanh::lean_unsigned_to_nat(12);
            return v___x_1300_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___boxed(
    mut v_x_1301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1302_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx(v_x_1301_);
    crate::leanh::lean_dec_ref(v_x_1301_);
    return v_res_1302_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
    mut v_t_1303_: *mut crate::leanh::LeanObject,
    mut v_k_1304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_1303_) {
        1 => {
            let mut v_e_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_thm_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_d_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_e_1305_ = crate::leanh::lean_ctor_get(v_t_1303_, 0);
            crate::leanh::lean_inc_ref(v_e_1305_);
            v_thm_1306_ = crate::leanh::lean_ctor_get(v_t_1303_, 1);
            crate::leanh::lean_inc_ref(v_thm_1306_);
            v_d_1307_ = crate::leanh::lean_ctor_get(v_t_1303_, 2);
            crate::leanh::lean_inc(v_d_1307_);
            v_a_1308_ = crate::leanh::lean_ctor_get(v_t_1303_, 3);
            crate::leanh::lean_inc_ref(v_a_1308_);
            crate::leanh::lean_dec_ref_known(v_t_1303_, 4);
            v___x_1309_ =
                crate::leanh::lean_apply_4(v_k_1304_, v_e_1305_, v_thm_1306_, v_d_1307_, v_a_1308_);
            return v___x_1309_;
        }
        4 => {
            let mut v_c_u2081_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_u2081_1310_ = crate::leanh::lean_ctor_get(v_t_1303_, 0);
            crate::leanh::lean_inc_ref(v_c_u2081_1310_);
            v_c_u2082_1311_ = crate::leanh::lean_ctor_get(v_t_1303_, 1);
            crate::leanh::lean_inc_ref(v_c_u2082_1311_);
            crate::leanh::lean_dec_ref_known(v_t_1303_, 2);
            v___x_1312_ = crate::leanh::lean_apply_2(v_k_1304_, v_c_u2081_1310_, v_c_u2082_1311_);
            return v___x_1312_;
        }
        5 => {
            let mut v_c_u2081_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_u2081_1313_ = crate::leanh::lean_ctor_get(v_t_1303_, 0);
            crate::leanh::lean_inc_ref(v_c_u2081_1313_);
            v_c_u2082_1314_ = crate::leanh::lean_ctor_get(v_t_1303_, 1);
            crate::leanh::lean_inc_ref(v_c_u2082_1314_);
            crate::leanh::lean_dec_ref_known(v_t_1303_, 2);
            v___x_1315_ = crate::leanh::lean_apply_2(v_k_1304_, v_c_u2081_1313_, v_c_u2082_1314_);
            return v___x_1315_;
        }
        7 => {
            let mut v_x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_1316_ = crate::leanh::lean_ctor_get(v_t_1303_, 0);
            crate::leanh::lean_inc(v_x_1316_);
            v_c_1317_ = crate::leanh::lean_ctor_get(v_t_1303_, 1);
            crate::leanh::lean_inc_ref(v_c_1317_);
            crate::leanh::lean_dec_ref_known(v_t_1303_, 2);
            v___x_1318_ = crate::leanh::lean_apply_2(v_k_1304_, v_x_1316_, v_c_1317_);
            return v___x_1318_;
        }
        8 => {
            let mut v_x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_1319_ = crate::leanh::lean_ctor_get(v_t_1303_, 0);
            crate::leanh::lean_inc(v_x_1319_);
            v_c_u2081_1320_ = crate::leanh::lean_ctor_get(v_t_1303_, 1);
            crate::leanh::lean_inc_ref(v_c_u2081_1320_);
            v_c_u2082_1321_ = crate::leanh::lean_ctor_get(v_t_1303_, 2);
            crate::leanh::lean_inc_ref(v_c_u2082_1321_);
            crate::leanh::lean_dec_ref_known(v_t_1303_, 3);
            v___x_1322_ =
                crate::leanh::lean_apply_3(v_k_1304_, v_x_1319_, v_c_u2081_1320_, v_c_u2082_1321_);
            return v___x_1322_;
        }
        12 => {
            let mut v_c_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_e_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_1323_ = crate::leanh::lean_ctor_get(v_t_1303_, 0);
            crate::leanh::lean_inc_ref(v_c_1323_);
            v_e_1324_ = crate::leanh::lean_ctor_get(v_t_1303_, 1);
            crate::leanh::lean_inc_ref(v_e_1324_);
            v_p_1325_ = crate::leanh::lean_ctor_get(v_t_1303_, 2);
            crate::leanh::lean_inc_ref(v_p_1325_);
            crate::leanh::lean_dec_ref_known(v_t_1303_, 3);
            v___x_1326_ = crate::leanh::lean_apply_3(v_k_1304_, v_c_1323_, v_e_1324_, v_p_1325_);
            return v___x_1326_;
        }
        _ => {
            let mut v_e_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_e_1327_ = crate::leanh::lean_ctor_get(v_t_1303_, 0);
            crate::leanh::lean_inc_ref(v_e_1327_);
            crate::leanh::lean_dec_ref(v_t_1303_);
            v___x_1328_ = crate::leanh::lean_apply_1(v_k_1304_, v_e_1327_);
            return v___x_1328_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(
    mut v_motive__7_1329_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1330_: *mut crate::leanh::LeanObject,
    mut v_t_1331_: *mut crate::leanh::LeanObject,
    mut v_h_1332_: *mut crate::leanh::LeanObject,
    mut v_k_1333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1334_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1331_, v_k_1333_);
    return v___x_1334_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___boxed(
    mut v_motive__7_1335_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1336_: *mut crate::leanh::LeanObject,
    mut v_t_1337_: *mut crate::leanh::LeanObject,
    mut v_h_1338_: *mut crate::leanh::LeanObject,
    mut v_k_1339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1340_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(
        v_motive__7_1335_,
        v_ctorIdx_1336_,
        v_t_1337_,
        v_h_1338_,
        v_k_1339_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1336_);
    return v_res_1340_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim___redArg(
    mut v_t_1341_: *mut crate::leanh::LeanObject,
    mut v_core_1342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1343_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1341_, v_core_1342_);
    return v___x_1343_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim(
    mut v_motive__7_1344_: *mut crate::leanh::LeanObject,
    mut v_t_1345_: *mut crate::leanh::LeanObject,
    mut v_h_1346_: *mut crate::leanh::LeanObject,
    mut v_core_1347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1348_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1345_, v_core_1347_);
    return v___x_1348_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim___redArg(
    mut v_t_1349_: *mut crate::leanh::LeanObject,
    mut v_coreOfNat_1350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1351_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1349_,
        v_coreOfNat_1350_,
    );
    return v___x_1351_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim(
    mut v_motive__7_1352_: *mut crate::leanh::LeanObject,
    mut v_t_1353_: *mut crate::leanh::LeanObject,
    mut v_h_1354_: *mut crate::leanh::LeanObject,
    mut v_coreOfNat_1355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1356_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1353_,
        v_coreOfNat_1355_,
    );
    return v___x_1356_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim___redArg(
    mut v_t_1357_: *mut crate::leanh::LeanObject,
    mut v_norm_1358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1359_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1357_, v_norm_1358_);
    return v___x_1359_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim(
    mut v_motive__7_1360_: *mut crate::leanh::LeanObject,
    mut v_t_1361_: *mut crate::leanh::LeanObject,
    mut v_h_1362_: *mut crate::leanh::LeanObject,
    mut v_norm_1363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1364_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1361_, v_norm_1363_);
    return v___x_1364_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim___redArg(
    mut v_t_1365_: *mut crate::leanh::LeanObject,
    mut v_divCoeffs_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1367_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1365_,
        v_divCoeffs_1366_,
    );
    return v___x_1367_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim(
    mut v_motive__7_1368_: *mut crate::leanh::LeanObject,
    mut v_t_1369_: *mut crate::leanh::LeanObject,
    mut v_h_1370_: *mut crate::leanh::LeanObject,
    mut v_divCoeffs_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1372_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1369_,
        v_divCoeffs_1371_,
    );
    return v___x_1372_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim___redArg(
    mut v_t_1373_: *mut crate::leanh::LeanObject,
    mut v_solveCombine_1374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1375_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1373_,
        v_solveCombine_1374_,
    );
    return v___x_1375_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim(
    mut v_motive__7_1376_: *mut crate::leanh::LeanObject,
    mut v_t_1377_: *mut crate::leanh::LeanObject,
    mut v_h_1378_: *mut crate::leanh::LeanObject,
    mut v_solveCombine_1379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1380_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1377_,
        v_solveCombine_1379_,
    );
    return v___x_1380_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim___redArg(
    mut v_t_1381_: *mut crate::leanh::LeanObject,
    mut v_solveElim_1382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1383_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1381_,
        v_solveElim_1382_,
    );
    return v___x_1383_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim(
    mut v_motive__7_1384_: *mut crate::leanh::LeanObject,
    mut v_t_1385_: *mut crate::leanh::LeanObject,
    mut v_h_1386_: *mut crate::leanh::LeanObject,
    mut v_solveElim_1387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1388_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1385_,
        v_solveElim_1387_,
    );
    return v___x_1388_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim___redArg(
    mut v_t_1389_: *mut crate::leanh::LeanObject,
    mut v_elim_1390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1391_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1389_, v_elim_1390_);
    return v___x_1391_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim(
    mut v_motive__7_1392_: *mut crate::leanh::LeanObject,
    mut v_t_1393_: *mut crate::leanh::LeanObject,
    mut v_h_1394_: *mut crate::leanh::LeanObject,
    mut v_elim_1395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1396_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1393_, v_elim_1395_);
    return v___x_1396_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEq_elim___redArg(
    mut v_t_1397_: *mut crate::leanh::LeanObject,
    mut v_ofEq_1398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1399_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1397_, v_ofEq_1398_);
    return v___x_1399_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEq_elim(
    mut v_motive__7_1400_: *mut crate::leanh::LeanObject,
    mut v_t_1401_: *mut crate::leanh::LeanObject,
    mut v_h_1402_: *mut crate::leanh::LeanObject,
    mut v_ofEq_1403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1401_, v_ofEq_1403_);
    return v___x_1404_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim___redArg(
    mut v_t_1405_: *mut crate::leanh::LeanObject,
    mut v_subst_1406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1407_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1405_, v_subst_1406_);
    return v___x_1407_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim(
    mut v_motive__7_1408_: *mut crate::leanh::LeanObject,
    mut v_t_1409_: *mut crate::leanh::LeanObject,
    mut v_h_1410_: *mut crate::leanh::LeanObject,
    mut v_subst_1411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1412_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1409_, v_subst_1411_);
    return v___x_1412_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim___redArg(
    mut v_t_1413_: *mut crate::leanh::LeanObject,
    mut v_cooper_u2081_1414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1415_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1413_,
        v_cooper_u2081_1414_,
    );
    return v___x_1415_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim(
    mut v_motive__7_1416_: *mut crate::leanh::LeanObject,
    mut v_t_1417_: *mut crate::leanh::LeanObject,
    mut v_h_1418_: *mut crate::leanh::LeanObject,
    mut v_cooper_u2081_1419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1420_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1417_,
        v_cooper_u2081_1419_,
    );
    return v___x_1420_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim___redArg(
    mut v_t_1421_: *mut crate::leanh::LeanObject,
    mut v_cooper_u2082_1422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1423_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1421_,
        v_cooper_u2082_1422_,
    );
    return v___x_1423_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim(
    mut v_motive__7_1424_: *mut crate::leanh::LeanObject,
    mut v_t_1425_: *mut crate::leanh::LeanObject,
    mut v_h_1426_: *mut crate::leanh::LeanObject,
    mut v_cooper_u2082_1427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1428_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1425_,
        v_cooper_u2082_1427_,
    );
    return v___x_1428_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim___redArg(
    mut v_t_1429_: *mut crate::leanh::LeanObject,
    mut v_reorder_1430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1431_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1429_, v_reorder_1430_);
    return v___x_1431_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim(
    mut v_motive__7_1432_: *mut crate::leanh::LeanObject,
    mut v_t_1433_: *mut crate::leanh::LeanObject,
    mut v_h_1434_: *mut crate::leanh::LeanObject,
    mut v_reorder_1435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1436_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1433_, v_reorder_1435_);
    return v___x_1436_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim___redArg(
    mut v_t_1437_: *mut crate::leanh::LeanObject,
    mut v_commRingNorm_1438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1439_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1437_,
        v_commRingNorm_1438_,
    );
    return v___x_1439_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim(
    mut v_motive__7_1440_: *mut crate::leanh::LeanObject,
    mut v_t_1441_: *mut crate::leanh::LeanObject,
    mut v_h_1442_: *mut crate::leanh::LeanObject,
    mut v_commRingNorm_1443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1444_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1441_,
        v_commRingNorm_1443_,
    );
    return v___x_1444_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx(
    mut v_x_1445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1445_) {
        0 => {
            let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1446_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1446_;
        }
        1 => {
            let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1447_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1447_;
        }
        2 => {
            let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1448_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1448_;
        }
        3 => {
            let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1449_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_1449_;
        }
        4 => {
            let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1450_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_1450_;
        }
        5 => {
            let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1451_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_1451_;
        }
        6 => {
            let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1452_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_1452_;
        }
        7 => {
            let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1453_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_1453_;
        }
        8 => {
            let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1454_ = crate::leanh::lean_unsigned_to_nat(8);
            return v___x_1454_;
        }
        9 => {
            let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1455_ = crate::leanh::lean_unsigned_to_nat(9);
            return v___x_1455_;
        }
        10 => {
            let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1456_ = crate::leanh::lean_unsigned_to_nat(10);
            return v___x_1456_;
        }
        11 => {
            let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1457_ = crate::leanh::lean_unsigned_to_nat(11);
            return v___x_1457_;
        }
        12 => {
            let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1458_ = crate::leanh::lean_unsigned_to_nat(12);
            return v___x_1458_;
        }
        13 => {
            let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1459_ = crate::leanh::lean_unsigned_to_nat(13);
            return v___x_1459_;
        }
        14 => {
            let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1460_ = crate::leanh::lean_unsigned_to_nat(14);
            return v___x_1460_;
        }
        15 => {
            let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1461_ = crate::leanh::lean_unsigned_to_nat(15);
            return v___x_1461_;
        }
        16 => {
            let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1462_ = crate::leanh::lean_unsigned_to_nat(16);
            return v___x_1462_;
        }
        _ => {
            let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1463_ = crate::leanh::lean_unsigned_to_nat(17);
            return v___x_1463_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___boxed(
    mut v_x_1464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1465_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx(v_x_1464_);
    crate::leanh::lean_dec_ref(v_x_1464_);
    return v_res_1465_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
    mut v_t_1466_: *mut crate::leanh::LeanObject,
    mut v_k_1467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_1466_) {
        1 => {
            let mut v_e_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_e_1468_ = crate::leanh::lean_ctor_get(v_t_1466_, 0);
            crate::leanh::lean_inc_ref(v_e_1468_);
            v_p_1469_ = crate::leanh::lean_ctor_get(v_t_1466_, 1);
            crate::leanh::lean_inc_ref(v_p_1469_);
            crate::leanh::lean_dec_ref_known(v_t_1466_, 2);
            v___x_1470_ = crate::leanh::lean_apply_2(v_k_1467_, v_e_1468_, v_p_1469_);
            return v___x_1470_;
        }
        2 => {
            let mut v_e_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_pos_1472_: u8 = 0;
            let mut v_toIntThm_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_e_1471_ = crate::leanh::lean_ctor_get(v_t_1466_, 0);
            crate::leanh::lean_inc_ref(v_e_1471_);
            v_pos_1472_ = crate::leanh::lean_ctor_get_uint8(
                v_t_1466_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
            );
            v_toIntThm_1473_ = crate::leanh::lean_ctor_get(v_t_1466_, 1);
            crate::leanh::lean_inc_ref(v_toIntThm_1473_);
            v_lhs_1474_ = crate::leanh::lean_ctor_get(v_t_1466_, 2);
            crate::leanh::lean_inc_ref(v_lhs_1474_);
            v_rhs_1475_ = crate::leanh::lean_ctor_get(v_t_1466_, 3);
            crate::leanh::lean_inc_ref(v_rhs_1475_);
            crate::leanh::lean_dec_ref_known(v_t_1466_, 4);
            v___x_1476_ = crate::leanh::lean_box((v_pos_1472_) as usize);
            v___x_1477_ = crate::leanh::lean_apply_5(
                v_k_1467_,
                v_e_1471_,
                v___x_1476_,
                v_toIntThm_1473_,
                v_lhs_1474_,
                v_rhs_1475_,
            );
            return v___x_1477_;
        }
        5 => {
            let mut v_h_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_h_1478_ = crate::leanh::lean_ctor_get(v_t_1466_, 0);
            crate::leanh::lean_inc(v_h_1478_);
            crate::leanh::lean_dec_ref_known(v_t_1466_, 1);
            v___x_1479_ = crate::leanh::lean_apply_1(v_k_1467_, v_h_1478_);
            return v___x_1479_;
        }
        8 => {
            let mut v_c_u2081_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_u2081_1480_ = crate::leanh::lean_ctor_get(v_t_1466_, 0);
            crate::leanh::lean_inc_ref(v_c_u2081_1480_);
            v_c_u2082_1481_ = crate::leanh::lean_ctor_get(v_t_1466_, 1);
            crate::leanh::lean_inc_ref(v_c_u2082_1481_);
            crate::leanh::lean_dec_ref_known(v_t_1466_, 2);
            v___x_1482_ = crate::leanh::lean_apply_2(v_k_1467_, v_c_u2081_1480_, v_c_u2082_1481_);
            return v___x_1482_;
        }
        9 => {
            let mut v_c_u2081_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_u2081_1483_ = crate::leanh::lean_ctor_get(v_t_1466_, 0);
            crate::leanh::lean_inc_ref(v_c_u2081_1483_);
            v_c_u2082_1484_ = crate::leanh::lean_ctor_get(v_t_1466_, 1);
            crate::leanh::lean_inc_ref(v_c_u2082_1484_);
            v_k_1485_ = crate::leanh::lean_ctor_get(v_t_1466_, 2);
            crate::leanh::lean_inc(v_k_1485_);
            crate::leanh::lean_dec_ref_known(v_t_1466_, 3);
            v___x_1486_ =
                crate::leanh::lean_apply_3(v_k_1467_, v_c_u2081_1483_, v_c_u2082_1484_, v_k_1485_);
            return v___x_1486_;
        }
        10 => {
            let mut v_x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_1487_ = crate::leanh::lean_ctor_get(v_t_1466_, 0);
            crate::leanh::lean_inc(v_x_1487_);
            v_c_u2081_1488_ = crate::leanh::lean_ctor_get(v_t_1466_, 1);
            crate::leanh::lean_inc_ref(v_c_u2081_1488_);
            v_c_u2082_1489_ = crate::leanh::lean_ctor_get(v_t_1466_, 2);
            crate::leanh::lean_inc_ref(v_c_u2082_1489_);
            crate::leanh::lean_dec_ref_known(v_t_1466_, 3);
            v___x_1490_ =
                crate::leanh::lean_apply_3(v_k_1467_, v_x_1487_, v_c_u2081_1488_, v_c_u2082_1489_);
            return v___x_1490_;
        }
        11 => {
            let mut v_c_u2081_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_u2081_1491_ = crate::leanh::lean_ctor_get(v_t_1466_, 0);
            crate::leanh::lean_inc_ref(v_c_u2081_1491_);
            v_c_u2082_1492_ = crate::leanh::lean_ctor_get(v_t_1466_, 1);
            crate::leanh::lean_inc_ref(v_c_u2082_1492_);
            crate::leanh::lean_dec_ref_known(v_t_1466_, 2);
            v___x_1493_ = crate::leanh::lean_apply_2(v_k_1467_, v_c_u2081_1491_, v_c_u2082_1492_);
            return v___x_1493_;
        }
        12 => {
            let mut v_c_u2081_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_decVar_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_h_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_decVars_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_u2081_1494_ = crate::leanh::lean_ctor_get(v_t_1466_, 0);
            crate::leanh::lean_inc_ref(v_c_u2081_1494_);
            v_decVar_1495_ = crate::leanh::lean_ctor_get(v_t_1466_, 1);
            crate::leanh::lean_inc(v_decVar_1495_);
            v_h_1496_ = crate::leanh::lean_ctor_get(v_t_1466_, 2);
            crate::leanh::lean_inc_ref(v_h_1496_);
            v_decVars_1497_ = crate::leanh::lean_ctor_get(v_t_1466_, 3);
            crate::leanh::lean_inc_ref(v_decVars_1497_);
            crate::leanh::lean_dec_ref_known(v_t_1466_, 4);
            v___x_1498_ = crate::leanh::lean_apply_4(
                v_k_1467_,
                v_c_u2081_1494_,
                v_decVar_1495_,
                v_h_1496_,
                v_decVars_1497_,
            );
            return v___x_1498_;
        }
        14 => {
            let mut v_c_u2081_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_u2081_1499_ = crate::leanh::lean_ctor_get(v_t_1466_, 0);
            crate::leanh::lean_inc_ref(v_c_u2081_1499_);
            v_c_u2082_1500_ = crate::leanh::lean_ctor_get(v_t_1466_, 1);
            crate::leanh::lean_inc_ref(v_c_u2082_1500_);
            crate::leanh::lean_dec_ref_known(v_t_1466_, 2);
            v___x_1501_ = crate::leanh::lean_apply_2(v_k_1467_, v_c_u2081_1499_, v_c_u2082_1500_);
            return v___x_1501_;
        }
        15 => {
            let mut v_c_u2081_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_u2081_1502_ = crate::leanh::lean_ctor_get(v_t_1466_, 0);
            crate::leanh::lean_inc_ref(v_c_u2081_1502_);
            v_c_u2082_1503_ = crate::leanh::lean_ctor_get(v_t_1466_, 1);
            crate::leanh::lean_inc_ref(v_c_u2082_1503_);
            crate::leanh::lean_dec_ref_known(v_t_1466_, 2);
            v___x_1504_ = crate::leanh::lean_apply_2(v_k_1467_, v_c_u2081_1502_, v_c_u2082_1503_);
            return v___x_1504_;
        }
        17 => {
            let mut v_c_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_e_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_1505_ = crate::leanh::lean_ctor_get(v_t_1466_, 0);
            crate::leanh::lean_inc_ref(v_c_1505_);
            v_e_1506_ = crate::leanh::lean_ctor_get(v_t_1466_, 1);
            crate::leanh::lean_inc_ref(v_e_1506_);
            v_p_1507_ = crate::leanh::lean_ctor_get(v_t_1466_, 2);
            crate::leanh::lean_inc_ref(v_p_1507_);
            crate::leanh::lean_dec_ref_known(v_t_1466_, 3);
            v___x_1508_ = crate::leanh::lean_apply_3(v_k_1467_, v_c_1505_, v_e_1506_, v_p_1507_);
            return v___x_1508_;
        }
        _ => {
            let mut v_e_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_e_1509_ = crate::leanh::lean_ctor_get(v_t_1466_, 0);
            crate::leanh::lean_inc_ref(v_e_1509_);
            crate::leanh::lean_dec_ref(v_t_1466_);
            v___x_1510_ = crate::leanh::lean_apply_1(v_k_1467_, v_e_1509_);
            return v___x_1510_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(
    mut v_motive__9_1511_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1512_: *mut crate::leanh::LeanObject,
    mut v_t_1513_: *mut crate::leanh::LeanObject,
    mut v_h_1514_: *mut crate::leanh::LeanObject,
    mut v_k_1515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1516_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1513_, v_k_1515_);
    return v___x_1516_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___boxed(
    mut v_motive__9_1517_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1518_: *mut crate::leanh::LeanObject,
    mut v_t_1519_: *mut crate::leanh::LeanObject,
    mut v_h_1520_: *mut crate::leanh::LeanObject,
    mut v_k_1521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1522_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(
        v_motive__9_1517_,
        v_ctorIdx_1518_,
        v_t_1519_,
        v_h_1520_,
        v_k_1521_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1518_);
    return v_res_1522_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim___redArg(
    mut v_t_1523_: *mut crate::leanh::LeanObject,
    mut v_core_1524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1525_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1523_, v_core_1524_);
    return v___x_1525_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim(
    mut v_motive__9_1526_: *mut crate::leanh::LeanObject,
    mut v_t_1527_: *mut crate::leanh::LeanObject,
    mut v_h_1528_: *mut crate::leanh::LeanObject,
    mut v_core_1529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1530_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1527_, v_core_1529_);
    return v___x_1530_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim___redArg(
    mut v_t_1531_: *mut crate::leanh::LeanObject,
    mut v_coreNeg_1532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1533_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1531_, v_coreNeg_1532_);
    return v___x_1533_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim(
    mut v_motive__9_1534_: *mut crate::leanh::LeanObject,
    mut v_t_1535_: *mut crate::leanh::LeanObject,
    mut v_h_1536_: *mut crate::leanh::LeanObject,
    mut v_coreNeg_1537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1538_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1535_, v_coreNeg_1537_);
    return v___x_1538_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim___redArg(
    mut v_t_1539_: *mut crate::leanh::LeanObject,
    mut v_coreToInt_1540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1541_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1539_, v_coreToInt_1540_);
    return v___x_1541_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim(
    mut v_motive__9_1542_: *mut crate::leanh::LeanObject,
    mut v_t_1543_: *mut crate::leanh::LeanObject,
    mut v_h_1544_: *mut crate::leanh::LeanObject,
    mut v_coreToInt_1545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1543_, v_coreToInt_1545_);
    return v___x_1546_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim___redArg(
    mut v_t_1547_: *mut crate::leanh::LeanObject,
    mut v_ofNatNonneg_1548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1549_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1547_,
        v_ofNatNonneg_1548_,
    );
    return v___x_1549_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim(
    mut v_motive__9_1550_: *mut crate::leanh::LeanObject,
    mut v_t_1551_: *mut crate::leanh::LeanObject,
    mut v_h_1552_: *mut crate::leanh::LeanObject,
    mut v_ofNatNonneg_1553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1554_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1551_,
        v_ofNatNonneg_1553_,
    );
    return v___x_1554_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim___redArg(
    mut v_t_1555_: *mut crate::leanh::LeanObject,
    mut v_bound_1556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1557_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1555_, v_bound_1556_);
    return v___x_1557_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim(
    mut v_motive__9_1558_: *mut crate::leanh::LeanObject,
    mut v_t_1559_: *mut crate::leanh::LeanObject,
    mut v_h_1560_: *mut crate::leanh::LeanObject,
    mut v_bound_1561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1562_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1559_, v_bound_1561_);
    return v___x_1562_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim___redArg(
    mut v_t_1563_: *mut crate::leanh::LeanObject,
    mut v_dec_1564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1565_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1563_, v_dec_1564_);
    return v___x_1565_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim(
    mut v_motive__9_1566_: *mut crate::leanh::LeanObject,
    mut v_t_1567_: *mut crate::leanh::LeanObject,
    mut v_h_1568_: *mut crate::leanh::LeanObject,
    mut v_dec_1569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1570_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1567_, v_dec_1569_);
    return v___x_1570_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim___redArg(
    mut v_t_1571_: *mut crate::leanh::LeanObject,
    mut v_norm_1572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1573_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1571_, v_norm_1572_);
    return v___x_1573_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim(
    mut v_motive__9_1574_: *mut crate::leanh::LeanObject,
    mut v_t_1575_: *mut crate::leanh::LeanObject,
    mut v_h_1576_: *mut crate::leanh::LeanObject,
    mut v_norm_1577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1578_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1575_, v_norm_1577_);
    return v___x_1578_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim___redArg(
    mut v_t_1579_: *mut crate::leanh::LeanObject,
    mut v_divCoeffs_1580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1581_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1579_, v_divCoeffs_1580_);
    return v___x_1581_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim(
    mut v_motive__9_1582_: *mut crate::leanh::LeanObject,
    mut v_t_1583_: *mut crate::leanh::LeanObject,
    mut v_h_1584_: *mut crate::leanh::LeanObject,
    mut v_divCoeffs_1585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1586_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1583_, v_divCoeffs_1585_);
    return v___x_1586_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim___redArg(
    mut v_t_1587_: *mut crate::leanh::LeanObject,
    mut v_combine_1588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1589_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1587_, v_combine_1588_);
    return v___x_1589_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim(
    mut v_motive__9_1590_: *mut crate::leanh::LeanObject,
    mut v_t_1591_: *mut crate::leanh::LeanObject,
    mut v_h_1592_: *mut crate::leanh::LeanObject,
    mut v_combine_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1594_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1591_, v_combine_1593_);
    return v___x_1594_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim___redArg(
    mut v_t_1595_: *mut crate::leanh::LeanObject,
    mut v_combineDivCoeffs_1596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1597_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1595_,
        v_combineDivCoeffs_1596_,
    );
    return v___x_1597_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim(
    mut v_motive__9_1598_: *mut crate::leanh::LeanObject,
    mut v_t_1599_: *mut crate::leanh::LeanObject,
    mut v_h_1600_: *mut crate::leanh::LeanObject,
    mut v_combineDivCoeffs_1601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1602_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1599_,
        v_combineDivCoeffs_1601_,
    );
    return v___x_1602_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim___redArg(
    mut v_t_1603_: *mut crate::leanh::LeanObject,
    mut v_subst_1604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1605_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1603_, v_subst_1604_);
    return v___x_1605_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim(
    mut v_motive__9_1606_: *mut crate::leanh::LeanObject,
    mut v_t_1607_: *mut crate::leanh::LeanObject,
    mut v_h_1608_: *mut crate::leanh::LeanObject,
    mut v_subst_1609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1610_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1607_, v_subst_1609_);
    return v___x_1610_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim___redArg(
    mut v_t_1611_: *mut crate::leanh::LeanObject,
    mut v_ofLeDiseq_1612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1613_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1611_, v_ofLeDiseq_1612_);
    return v___x_1613_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim(
    mut v_motive__9_1614_: *mut crate::leanh::LeanObject,
    mut v_t_1615_: *mut crate::leanh::LeanObject,
    mut v_h_1616_: *mut crate::leanh::LeanObject,
    mut v_ofLeDiseq_1617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1618_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1615_, v_ofLeDiseq_1617_);
    return v___x_1618_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim___redArg(
    mut v_t_1619_: *mut crate::leanh::LeanObject,
    mut v_ofDiseqSplit_1620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1621_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1619_,
        v_ofDiseqSplit_1620_,
    );
    return v___x_1621_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim(
    mut v_motive__9_1622_: *mut crate::leanh::LeanObject,
    mut v_t_1623_: *mut crate::leanh::LeanObject,
    mut v_h_1624_: *mut crate::leanh::LeanObject,
    mut v_ofDiseqSplit_1625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1626_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1623_,
        v_ofDiseqSplit_1625_,
    );
    return v___x_1626_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim___redArg(
    mut v_t_1627_: *mut crate::leanh::LeanObject,
    mut v_cooper_1628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1629_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1627_, v_cooper_1628_);
    return v___x_1629_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim(
    mut v_motive__9_1630_: *mut crate::leanh::LeanObject,
    mut v_t_1631_: *mut crate::leanh::LeanObject,
    mut v_h_1632_: *mut crate::leanh::LeanObject,
    mut v_cooper_1633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1634_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1631_, v_cooper_1633_);
    return v___x_1634_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTight_elim___redArg(
    mut v_t_1635_: *mut crate::leanh::LeanObject,
    mut v_dvdTight_1636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1637_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1635_, v_dvdTight_1636_);
    return v___x_1637_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTight_elim(
    mut v_motive__9_1638_: *mut crate::leanh::LeanObject,
    mut v_t_1639_: *mut crate::leanh::LeanObject,
    mut v_h_1640_: *mut crate::leanh::LeanObject,
    mut v_dvdTight_1641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1642_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1639_, v_dvdTight_1641_);
    return v___x_1642_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_negDvdTight_elim___redArg(
    mut v_t_1643_: *mut crate::leanh::LeanObject,
    mut v_negDvdTight_1644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1645_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1643_,
        v_negDvdTight_1644_,
    );
    return v___x_1645_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_negDvdTight_elim(
    mut v_motive__9_1646_: *mut crate::leanh::LeanObject,
    mut v_t_1647_: *mut crate::leanh::LeanObject,
    mut v_h_1648_: *mut crate::leanh::LeanObject,
    mut v_negDvdTight_1649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1650_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1647_,
        v_negDvdTight_1649_,
    );
    return v___x_1650_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim___redArg(
    mut v_t_1651_: *mut crate::leanh::LeanObject,
    mut v_reorder_1652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1653_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1651_, v_reorder_1652_);
    return v___x_1653_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim(
    mut v_motive__9_1654_: *mut crate::leanh::LeanObject,
    mut v_t_1655_: *mut crate::leanh::LeanObject,
    mut v_h_1656_: *mut crate::leanh::LeanObject,
    mut v_reorder_1657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1658_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1655_, v_reorder_1657_);
    return v___x_1658_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim___redArg(
    mut v_t_1659_: *mut crate::leanh::LeanObject,
    mut v_commRingNorm_1660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1661_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1659_,
        v_commRingNorm_1660_,
    );
    return v___x_1661_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim(
    mut v_motive__9_1662_: *mut crate::leanh::LeanObject,
    mut v_t_1663_: *mut crate::leanh::LeanObject,
    mut v_h_1664_: *mut crate::leanh::LeanObject,
    mut v_commRingNorm_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1666_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1663_,
        v_commRingNorm_1665_,
    );
    return v___x_1666_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx(
    mut v_x_1667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1667_) {
        0 => {
            let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1668_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1668_;
        }
        1 => {
            let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1669_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1669_;
        }
        2 => {
            let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1670_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1670_;
        }
        3 => {
            let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1671_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_1671_;
        }
        4 => {
            let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1672_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_1672_;
        }
        5 => {
            let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1673_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_1673_;
        }
        6 => {
            let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1674_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_1674_;
        }
        7 => {
            let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1675_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_1675_;
        }
        _ => {
            let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1676_ = crate::leanh::lean_unsigned_to_nat(8);
            return v___x_1676_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___boxed(
    mut v_x_1677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1678_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx(v_x_1677_);
    crate::leanh::lean_dec_ref(v_x_1677_);
    return v_res_1678_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(
    mut v_t_1679_: *mut crate::leanh::LeanObject,
    mut v_k_1680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_1679_) {
        0 => {
            let mut v_a_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_zero_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1681_ = crate::leanh::lean_ctor_get(v_t_1679_, 0);
            crate::leanh::lean_inc_ref(v_a_1681_);
            v_zero_1682_ = crate::leanh::lean_ctor_get(v_t_1679_, 1);
            crate::leanh::lean_inc_ref(v_zero_1682_);
            crate::leanh::lean_dec_ref_known(v_t_1679_, 2);
            v___x_1683_ = crate::leanh::lean_apply_2(v_k_1680_, v_a_1681_, v_zero_1682_);
            return v___x_1683_;
        }
        1 => {
            let mut v_a_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_u2081_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_u2082_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1684_ = crate::leanh::lean_ctor_get(v_t_1679_, 0);
            crate::leanh::lean_inc_ref(v_a_1684_);
            v_b_1685_ = crate::leanh::lean_ctor_get(v_t_1679_, 1);
            crate::leanh::lean_inc_ref(v_b_1685_);
            v_p_u2081_1686_ = crate::leanh::lean_ctor_get(v_t_1679_, 2);
            crate::leanh::lean_inc_ref(v_p_u2081_1686_);
            v_p_u2082_1687_ = crate::leanh::lean_ctor_get(v_t_1679_, 3);
            crate::leanh::lean_inc_ref(v_p_u2082_1687_);
            crate::leanh::lean_dec_ref_known(v_t_1679_, 4);
            v___x_1688_ = crate::leanh::lean_apply_4(
                v_k_1680_,
                v_a_1684_,
                v_b_1685_,
                v_p_u2081_1686_,
                v_p_u2082_1687_,
            );
            return v___x_1688_;
        }
        2 => {
            let mut v_a_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toIntThm_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1689_ = crate::leanh::lean_ctor_get(v_t_1679_, 0);
            crate::leanh::lean_inc_ref(v_a_1689_);
            v_b_1690_ = crate::leanh::lean_ctor_get(v_t_1679_, 1);
            crate::leanh::lean_inc_ref(v_b_1690_);
            v_toIntThm_1691_ = crate::leanh::lean_ctor_get(v_t_1679_, 2);
            crate::leanh::lean_inc_ref(v_toIntThm_1691_);
            v_lhs_1692_ = crate::leanh::lean_ctor_get(v_t_1679_, 3);
            crate::leanh::lean_inc_ref(v_lhs_1692_);
            v_rhs_1693_ = crate::leanh::lean_ctor_get(v_t_1679_, 4);
            crate::leanh::lean_inc_ref(v_rhs_1693_);
            crate::leanh::lean_dec_ref_known(v_t_1679_, 5);
            v___x_1694_ = crate::leanh::lean_apply_5(
                v_k_1680_,
                v_a_1689_,
                v_b_1690_,
                v_toIntThm_1691_,
                v_lhs_1692_,
                v_rhs_1693_,
            );
            return v___x_1694_;
        }
        6 => {
            let mut v_x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_1695_ = crate::leanh::lean_ctor_get(v_t_1679_, 0);
            crate::leanh::lean_inc(v_x_1695_);
            v_c_u2081_1696_ = crate::leanh::lean_ctor_get(v_t_1679_, 1);
            crate::leanh::lean_inc_ref(v_c_u2081_1696_);
            v_c_u2082_1697_ = crate::leanh::lean_ctor_get(v_t_1679_, 2);
            crate::leanh::lean_inc_ref(v_c_u2082_1697_);
            crate::leanh::lean_dec_ref_known(v_t_1679_, 3);
            v___x_1698_ =
                crate::leanh::lean_apply_3(v_k_1680_, v_x_1695_, v_c_u2081_1696_, v_c_u2082_1697_);
            return v___x_1698_;
        }
        8 => {
            let mut v_c_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_e_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_1699_ = crate::leanh::lean_ctor_get(v_t_1679_, 0);
            crate::leanh::lean_inc_ref(v_c_1699_);
            v_e_1700_ = crate::leanh::lean_ctor_get(v_t_1679_, 1);
            crate::leanh::lean_inc_ref(v_e_1700_);
            v_p_1701_ = crate::leanh::lean_ctor_get(v_t_1679_, 2);
            crate::leanh::lean_inc_ref(v_p_1701_);
            crate::leanh::lean_dec_ref_known(v_t_1679_, 3);
            v___x_1702_ = crate::leanh::lean_apply_3(v_k_1680_, v_c_1699_, v_e_1700_, v_p_1701_);
            return v___x_1702_;
        }
        _ => {
            let mut v_c_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_1703_ = crate::leanh::lean_ctor_get(v_t_1679_, 0);
            crate::leanh::lean_inc_ref(v_c_1703_);
            crate::leanh::lean_dec_ref(v_t_1679_);
            v___x_1704_ = crate::leanh::lean_apply_1(v_k_1680_, v_c_1703_);
            return v___x_1704_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(
    mut v_motive__11_1705_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1706_: *mut crate::leanh::LeanObject,
    mut v_t_1707_: *mut crate::leanh::LeanObject,
    mut v_h_1708_: *mut crate::leanh::LeanObject,
    mut v_k_1709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1710_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1707_, v_k_1709_);
    return v___x_1710_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___boxed(
    mut v_motive__11_1711_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1712_: *mut crate::leanh::LeanObject,
    mut v_t_1713_: *mut crate::leanh::LeanObject,
    mut v_h_1714_: *mut crate::leanh::LeanObject,
    mut v_k_1715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1716_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(
        v_motive__11_1711_,
        v_ctorIdx_1712_,
        v_t_1713_,
        v_h_1714_,
        v_k_1715_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1712_);
    return v_res_1716_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim___redArg(
    mut v_t_1717_: *mut crate::leanh::LeanObject,
    mut v_core0_1718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1719_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1717_, v_core0_1718_);
    return v___x_1719_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim(
    mut v_motive__11_1720_: *mut crate::leanh::LeanObject,
    mut v_t_1721_: *mut crate::leanh::LeanObject,
    mut v_h_1722_: *mut crate::leanh::LeanObject,
    mut v_core0_1723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1724_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1721_, v_core0_1723_);
    return v___x_1724_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim___redArg(
    mut v_t_1725_: *mut crate::leanh::LeanObject,
    mut v_core_1726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1727_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1725_, v_core_1726_);
    return v___x_1727_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim(
    mut v_motive__11_1728_: *mut crate::leanh::LeanObject,
    mut v_t_1729_: *mut crate::leanh::LeanObject,
    mut v_h_1730_: *mut crate::leanh::LeanObject,
    mut v_core_1731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1732_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1729_, v_core_1731_);
    return v___x_1732_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim___redArg(
    mut v_t_1733_: *mut crate::leanh::LeanObject,
    mut v_coreToInt_1734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1735_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(
        v_t_1733_,
        v_coreToInt_1734_,
    );
    return v___x_1735_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim(
    mut v_motive__11_1736_: *mut crate::leanh::LeanObject,
    mut v_t_1737_: *mut crate::leanh::LeanObject,
    mut v_h_1738_: *mut crate::leanh::LeanObject,
    mut v_coreToInt_1739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1740_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(
        v_t_1737_,
        v_coreToInt_1739_,
    );
    return v___x_1740_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim___redArg(
    mut v_t_1741_: *mut crate::leanh::LeanObject,
    mut v_norm_1742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1743_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1741_, v_norm_1742_);
    return v___x_1743_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim(
    mut v_motive__11_1744_: *mut crate::leanh::LeanObject,
    mut v_t_1745_: *mut crate::leanh::LeanObject,
    mut v_h_1746_: *mut crate::leanh::LeanObject,
    mut v_norm_1747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1748_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1745_, v_norm_1747_);
    return v___x_1748_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim___redArg(
    mut v_t_1749_: *mut crate::leanh::LeanObject,
    mut v_divCoeffs_1750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1751_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(
        v_t_1749_,
        v_divCoeffs_1750_,
    );
    return v___x_1751_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim(
    mut v_motive__11_1752_: *mut crate::leanh::LeanObject,
    mut v_t_1753_: *mut crate::leanh::LeanObject,
    mut v_h_1754_: *mut crate::leanh::LeanObject,
    mut v_divCoeffs_1755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1756_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(
        v_t_1753_,
        v_divCoeffs_1755_,
    );
    return v___x_1756_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim___redArg(
    mut v_t_1757_: *mut crate::leanh::LeanObject,
    mut v_neg_1758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1759_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1757_, v_neg_1758_);
    return v___x_1759_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim(
    mut v_motive__11_1760_: *mut crate::leanh::LeanObject,
    mut v_t_1761_: *mut crate::leanh::LeanObject,
    mut v_h_1762_: *mut crate::leanh::LeanObject,
    mut v_neg_1763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1764_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1761_, v_neg_1763_);
    return v___x_1764_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim___redArg(
    mut v_t_1765_: *mut crate::leanh::LeanObject,
    mut v_subst_1766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1767_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1765_, v_subst_1766_);
    return v___x_1767_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim(
    mut v_motive__11_1768_: *mut crate::leanh::LeanObject,
    mut v_t_1769_: *mut crate::leanh::LeanObject,
    mut v_h_1770_: *mut crate::leanh::LeanObject,
    mut v_subst_1771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1772_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1769_, v_subst_1771_);
    return v___x_1772_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim___redArg(
    mut v_t_1773_: *mut crate::leanh::LeanObject,
    mut v_reorder_1774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1775_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(
        v_t_1773_,
        v_reorder_1774_,
    );
    return v___x_1775_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim(
    mut v_motive__11_1776_: *mut crate::leanh::LeanObject,
    mut v_t_1777_: *mut crate::leanh::LeanObject,
    mut v_h_1778_: *mut crate::leanh::LeanObject,
    mut v_reorder_1779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1780_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(
        v_t_1777_,
        v_reorder_1779_,
    );
    return v___x_1780_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim___redArg(
    mut v_t_1781_: *mut crate::leanh::LeanObject,
    mut v_commRingNorm_1782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1783_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(
        v_t_1781_,
        v_commRingNorm_1782_,
    );
    return v___x_1783_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim(
    mut v_motive__11_1784_: *mut crate::leanh::LeanObject,
    mut v_t_1785_: *mut crate::leanh::LeanObject,
    mut v_h_1786_: *mut crate::leanh::LeanObject,
    mut v_commRingNorm_1787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1788_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(
        v_t_1785_,
        v_commRingNorm_1787_,
    );
    return v___x_1788_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx(
    mut v_x_1789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1789_) {
        0 => {
            let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1790_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1790_;
        }
        1 => {
            let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1791_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1791_;
        }
        2 => {
            let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1792_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1792_;
        }
        3 => {
            let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1793_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_1793_;
        }
        _ => {
            let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1794_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_1794_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___boxed(
    mut v_x_1795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1796_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx(v_x_1795_);
    crate::leanh::lean_dec_ref(v_x_1795_);
    return v_res_1796_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(
    mut v_t_1797_: *mut crate::leanh::LeanObject,
    mut v_k_1798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1797_) == 4 {
        let mut v_c_u2081_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_c_u2082_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_c_u2083_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_c_u2081_1799_ = crate::leanh::lean_ctor_get(v_t_1797_, 0);
        crate::leanh::lean_inc_ref(v_c_u2081_1799_);
        v_c_u2082_1800_ = crate::leanh::lean_ctor_get(v_t_1797_, 1);
        crate::leanh::lean_inc_ref(v_c_u2082_1800_);
        v_c_u2083_1801_ = crate::leanh::lean_ctor_get(v_t_1797_, 2);
        crate::leanh::lean_inc_ref(v_c_u2083_1801_);
        crate::leanh::lean_dec_ref_known(v_t_1797_, 3);
        v___x_1802_ = crate::leanh::lean_apply_3(
            v_k_1798_,
            v_c_u2081_1799_,
            v_c_u2082_1800_,
            v_c_u2083_1801_,
        );
        return v___x_1802_;
    } else {
        let mut v_c_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_c_1803_ = crate::leanh::lean_ctor_get(v_t_1797_, 0);
        crate::leanh::lean_inc_ref(v_c_1803_);
        crate::leanh::lean_dec_ref(v_t_1797_);
        v___x_1804_ = crate::leanh::lean_apply_1(v_k_1798_, v_c_1803_);
        return v___x_1804_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(
    mut v_motive__12_1805_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1806_: *mut crate::leanh::LeanObject,
    mut v_t_1807_: *mut crate::leanh::LeanObject,
    mut v_h_1808_: *mut crate::leanh::LeanObject,
    mut v_k_1809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1810_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1807_, v_k_1809_);
    return v___x_1810_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___boxed(
    mut v_motive__12_1811_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1812_: *mut crate::leanh::LeanObject,
    mut v_t_1813_: *mut crate::leanh::LeanObject,
    mut v_h_1814_: *mut crate::leanh::LeanObject,
    mut v_k_1815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1816_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(
        v_motive__12_1811_,
        v_ctorIdx_1812_,
        v_t_1813_,
        v_h_1814_,
        v_k_1815_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1812_);
    return v_res_1816_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim___redArg(
    mut v_t_1817_: *mut crate::leanh::LeanObject,
    mut v_dvd_1818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1819_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1817_, v_dvd_1818_);
    return v___x_1819_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim(
    mut v_motive__12_1820_: *mut crate::leanh::LeanObject,
    mut v_t_1821_: *mut crate::leanh::LeanObject,
    mut v_h_1822_: *mut crate::leanh::LeanObject,
    mut v_dvd_1823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1824_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1821_, v_dvd_1823_);
    return v___x_1824_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim___redArg(
    mut v_t_1825_: *mut crate::leanh::LeanObject,
    mut v_le_1826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1827_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1825_, v_le_1826_);
    return v___x_1827_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim(
    mut v_motive__12_1828_: *mut crate::leanh::LeanObject,
    mut v_t_1829_: *mut crate::leanh::LeanObject,
    mut v_h_1830_: *mut crate::leanh::LeanObject,
    mut v_le_1831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1832_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1829_, v_le_1831_);
    return v___x_1832_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim___redArg(
    mut v_t_1833_: *mut crate::leanh::LeanObject,
    mut v_eq_1834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1835_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1833_, v_eq_1834_);
    return v___x_1835_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim(
    mut v_motive__12_1836_: *mut crate::leanh::LeanObject,
    mut v_t_1837_: *mut crate::leanh::LeanObject,
    mut v_h_1838_: *mut crate::leanh::LeanObject,
    mut v_eq_1839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1840_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1837_, v_eq_1839_);
    return v___x_1840_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim___redArg(
    mut v_t_1841_: *mut crate::leanh::LeanObject,
    mut v_diseq_1842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1843_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1841_, v_diseq_1842_);
    return v___x_1843_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim(
    mut v_motive__12_1844_: *mut crate::leanh::LeanObject,
    mut v_t_1845_: *mut crate::leanh::LeanObject,
    mut v_h_1846_: *mut crate::leanh::LeanObject,
    mut v_diseq_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1848_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1845_, v_diseq_1847_);
    return v___x_1848_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim___redArg(
    mut v_t_1849_: *mut crate::leanh::LeanObject,
    mut v_cooper_1850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1851_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1849_, v_cooper_1850_);
    return v___x_1851_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim(
    mut v_motive__12_1852_: *mut crate::leanh::LeanObject,
    mut v_t_1853_: *mut crate::leanh::LeanObject,
    mut v_h_1854_: *mut crate::leanh::LeanObject,
    mut v_cooper_1855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1856_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1853_, v_cooper_1855_);
    return v___x_1856_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1857_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0,
    );
    v___x_1858_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1858_, 0, v___x_1857_);
    return v___x_1858_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1862_ = crate::leanh::lean_box(0);
    v___x_1863_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2;
    v___x_1864_ = l_Lean_Expr_const___override(v___x_1863_, v___x_1862_);
    return v___x_1864_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1865_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3,
    );
    v___x_1866_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1866_, 0, v___x_1865_);
    return v___x_1866_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1867_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4,
    );
    v___x_1868_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0,
    );
    v___x_1869_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1869_, 0, v___x_1868_);
    crate::leanh::lean_ctor_set(v___x_1869_, 1, v___x_1867_);
    return v___x_1869_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1870_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5,
    );
    return v___x_1870_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1871_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3,
    );
    v___x_1872_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1872_, 0, v___x_1871_);
    return v___x_1872_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1873_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0,
    );
    v___x_1874_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0,
    );
    v___x_1875_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0,
    );
    v___x_1876_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1876_, 0, v___x_1875_);
    crate::leanh::lean_ctor_set(v___x_1876_, 1, v___x_1874_);
    crate::leanh::lean_ctor_set(v___x_1876_, 2, v___x_1873_);
    return v___x_1876_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1877_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1,
    );
    return v___x_1877_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: u8 = 0;
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1878_ = crate::leanh::lean_box(0);
    v___x_1879_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5,
    );
    v___x_1880_ = 0;
    v___x_1881_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1881_, 0, v___x_1879_);
    crate::leanh::lean_ctor_set(v___x_1881_, 1, v___x_1879_);
    crate::leanh::lean_ctor_set(v___x_1881_, 2, v___x_1878_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1881_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1880_,
    );
    return v___x_1881_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1882_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0,
    );
    return v___x_1882_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1885_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0;
    v___x_1886_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1887_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0,
    );
    v___x_1888_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1888_, 0, v___x_1887_);
    crate::leanh::lean_ctor_set(v___x_1888_, 1, v___x_1886_);
    crate::leanh::lean_ctor_set(v___x_1888_, 2, v___x_1885_);
    return v___x_1888_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1889_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1,
    );
    return v___x_1889_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1890_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1890_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1891_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0);
    v___x_1892_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1892_, 0, v___x_1891_);
    return v___x_1892_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0(
    mut v_00_u03b2_1893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1894_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1);
    return v___x_1894_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1895_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1896_ = lean_mk_empty_array_with_capacity(v___x_1895_);
    v___x_1897_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1897_, 0, v___x_1896_);
    return v___x_1897_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1898_: usize = 0;
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1898_ = 5usize;
    v___x_1899_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1900_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1901_ = lean_mk_empty_array_with_capacity(v___x_1900_);
    v___x_1902_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0,
    );
    v___x_1903_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1903_, 0, v___x_1902_);
    crate::leanh::lean_ctor_set(v___x_1903_, 1, v___x_1901_);
    crate::leanh::lean_ctor_set(v___x_1903_, 2, v___x_1899_);
    crate::leanh::lean_ctor_set(v___x_1903_, 3, v___x_1899_);
    crate::leanh::lean_ctor_set_usize(v___x_1903_, 4, v___x_1898_);
    return v___x_1903_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1904_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1904_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1905_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2,
    );
    v___x_1906_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1906_, 0, v___x_1905_);
    return v___x_1906_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1907_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0(crate::leanh::lean_box(0));
    return v___x_1907_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: u8 = 0;
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1908_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4,
    );
    v___x_1909_ = crate::leanh::lean_box(0);
    v___x_1910_ = 0;
    v___x_1911_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1912_ = crate::leanh::lean_box(0);
    v___x_1913_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3,
    );
    v___x_1914_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1,
    );
    v___x_1915_ = crate::leanh::lean_alloc_ctor(0, 23, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1915_, 0, v___x_1914_);
    crate::leanh::lean_ctor_set(v___x_1915_, 1, v___x_1913_);
    crate::leanh::lean_ctor_set(v___x_1915_, 2, v___x_1914_);
    crate::leanh::lean_ctor_set(v___x_1915_, 3, v___x_1913_);
    crate::leanh::lean_ctor_set(v___x_1915_, 4, v___x_1913_);
    crate::leanh::lean_ctor_set(v___x_1915_, 5, v___x_1913_);
    crate::leanh::lean_ctor_set(v___x_1915_, 6, v___x_1914_);
    crate::leanh::lean_ctor_set(v___x_1915_, 7, v___x_1914_);
    crate::leanh::lean_ctor_set(v___x_1915_, 8, v___x_1914_);
    crate::leanh::lean_ctor_set(v___x_1915_, 9, v___x_1914_);
    crate::leanh::lean_ctor_set(v___x_1915_, 10, v___x_1914_);
    crate::leanh::lean_ctor_set(v___x_1915_, 11, v___x_1912_);
    crate::leanh::lean_ctor_set(v___x_1915_, 12, v___x_1914_);
    crate::leanh::lean_ctor_set(v___x_1915_, 13, v___x_1914_);
    crate::leanh::lean_ctor_set(v___x_1915_, 14, v___x_1911_);
    crate::leanh::lean_ctor_set(v___x_1915_, 15, v___x_1909_);
    crate::leanh::lean_ctor_set(v___x_1915_, 16, v___x_1913_);
    crate::leanh::lean_ctor_set(v___x_1915_, 17, v___x_1908_);
    crate::leanh::lean_ctor_set(v___x_1915_, 18, v___x_1913_);
    crate::leanh::lean_ctor_set(v___x_1915_, 19, v___x_1914_);
    crate::leanh::lean_ctor_set(v___x_1915_, 20, v___x_1913_);
    crate::leanh::lean_ctor_set(v___x_1915_, 21, v___x_1913_);
    crate::leanh::lean_ctor_set(v___x_1915_, 22, v___x_1913_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1915_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23) as u32,
        v___x_1910_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1915_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23 + 1) as u32,
        v___x_1910_,
    );
    return v___x_1915_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1916_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5,
    );
    return v___x_1916_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1917_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
    return v___x_1917_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(
    mut v___x_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1920_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1920_, 0, v___x_1918_);
    return v___x_1920_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(
    mut v___x_1921_: *mut crate::leanh::LeanObject,
    mut v___y_1922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1923_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(v___x_1921_);
    return v_res_1923_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1924_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5,
    );
    v___f_1925_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_1925_, 0, v___x_1924_);
    return v___f_1925_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1927_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_);
    v___x_1928_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_1927_);
    return v___x_1928_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(
    mut v_a_1929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1930_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_();
    return v_res_1930_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr);
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr);
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred);
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit);
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default);
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
}
